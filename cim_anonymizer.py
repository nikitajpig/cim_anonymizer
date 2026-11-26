#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Потоковое обезличивание CIM RDF/XML без загрузки всей модели в память."""
from __future__ import annotations
import argparse
import hashlib
import hmac
import io
import json
import os
import re
import sqlite3
import sys
import tempfile
import time
import uuid
import zipfile
from collections import Counter
from pathlib import Path
from typing import BinaryIO, Optional

from lxml import etree

RDF_NS = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
RDF_ABOUT = f"{{{RDF_NS}}}about"
RDF_RESOURCE = f"{{{RDF_NS}}}resource"
RDF_ID = f"{{{RDF_NS}}}ID"
RDF_NODEID = f"{{{RDF_NS}}}nodeID"

# Короткие синтетические прилагательные и типовые обозначения классов.
ADJECTIVES = [
    "Абрикосовая", "Яблочная", "Грушёвая", "Сливовая", "Вишнёвая",
    "Персиковая", "Айвовая", "Морковная", "Тыквенная", "Редисовая",
    "Капустная", "Свекольная", "Огуречная", "Дынная", "Черешневая",
    "Малиновая", "Клубничная", "Брусничная", "Клюквенная", "Лимонная",
    "Апельсиновая", "Мандариновая", "Гранатовая", "Финиковая", "Инжирная",
]
FIRST_NAMES = ["Александр", "Алексей", "Андрей", "Антон", "Артём", "Борис", "Вадим", "Валерий", "Виктор", "Виталий", "Владимир", "Георгий", "Даниил", "Денис", "Дмитрий", "Евгений", "Иван", "Игорь", "Кирилл", "Константин", "Максим", "Михаил", "Никита", "Олег", "Павел", "Роман", "Сергей", "Тимофей", "Фёдор"]
_LAST_NAMES = ["Алексеев", "Андреев", "Белов", "Борисов", "Васильев", "Волков", "Гаврилов", "Громов", "Данилов", "Демидов", "Егоров", "Жуков", "Зайцев", "Ильин", "Калинин", "Козлов", "Комаров", "Крылов", "Лебедев", "Макаров", "Миронов", "Морозов", "Никитин", "Орлов", "Павлов", "Петров", "Романов", "Соколов", "Фёдоров", "Яковлев"]
_PATRONYMICS = ["Александрович", "Алексеевич", "Андреевич", "Борисович", "Вадимович", "Викторович", "Владимирович", "Георгиевич", "Дмитриевич", "Евгеньевич", "Иванович", "Игоревич", "Кириллович", "Максимович", "Михайлович", "Олегович", "Павлович", "Романович", "Сергеевич", "Фёдорович"]

PRESERVE_NAME_CLASSES = {
    # Справочники и технические классификаторы: их названия несут семантику, а не имя объекта.
    "BaseVoltage", "PSRType", "Position", "Department", "NameType", "RoleCategory",
    "ElectricalSafetyLevel", "AltitudinalSafetyLevel", "ConfinedSpaceSafetyLevel",
    "OperationalLimitType", "OperationalLimitSetType", "MeasurementType",
    "MeasurementValueType", "UnitLabel", "OMSCustomerKind", "ServiceDispCategory",
    "ServiceContingencyCategory", "DefectKind", "DocumentType", "MarkerType",
    "MarkerFunction", "ShiftRole", "RTDBEventLevel", "RTDBEventCategory",
    "RTDBEventType", "AggregationMethod", "TransitionDataType", "VCTimeZone",
    "ViolationSeverity", "ViolationRelevance", "ViolatedLimitType", "RCDMethod",
    "OrganisationRole", "OperationalAuthority", "Season", "DayType",
}

CLASS_PREFIX = {
    "Substation": "ПС", "VoltageLevel": "УРОВЕНЬ", "Bay": "ЯЧЕЙКА",
    "ACLineSegment": "ЛЭП", "PowerTransformer": "ТРАНСФОРМАТОР",
    "PowerTransformerEnd": "ОБМОТКА", "Pole": "ОПОРА",
    "ConnectivityNode": "УЗЕЛ", "Terminal": "ПРИСОЕДИНЕНИЕ",
    "BusbarSection": "ШИНА", "Breaker": "ВЫКЛЮЧАТЕЛЬ",
    "Disconnector": "РАЗЪЕДИНИТЕЛЬ", "LoadBreakSwitch": "ВЫКЛЮЧАТЕЛЬ",
    "Fuse": "ПРЕДОХРАНИТЕЛЬ", "Plant": "ПЛОЩАДКА",
    "GeographicalRegion": "РАЙОН", "SubGeographicalRegion": "УЧАСТОК",
    "ServiceLocation": "ТОЧКА_ОБСЛУЖИВАНИЯ", "UsagePoint": "ТОЧКА_УЧЁТА",
    "Customer": "АБОНЕНТ", "Organisation": "ОРГАНИЗАЦИЯ",
    "Person": "СОТРУДНИК", "Asset": "ИМУЩЕСТВО", "Meter": "СЧЁТЧИК",
}

PERSON_FIELDS = {"Person.firstName", "Person.lastName", "Person.middleName", "Person.patronymic", "Person.fullName", "Location.inChargeFullName"}
ADDRESS_FIELDS = {"Location.mainAddress", "StreetAddress.streetName", "StreetAddress.townDetail", "StreetAddress.postalCode", "Location.address"}
ID_FIELDS_EXACT = {"IdentifiedObject.mRID", "IdentifiedObject.mRIDStr", "Asset.serialNumber", "Meter.meteringPointCode"}

EMAIL_RE = re.compile(r"(?i)\b[A-Z0-9._%+-]+@[A-Z0-9.-]+\.[A-Z]{2,}\b")
PHONE_RE = re.compile(r"(?<!\w)(?:\+?\d[\d\s()\-]{7,}\d)(?!\w)")
PASSPORT_RE = re.compile(r"(?<!\d)(\d{2})\s?(\d{2})\s?(\d{6})(?!\d)")
INN_RE = re.compile(r"(?<!\d)\d{10}(?:\d{2})?(?!\d)")

class PrefixedReader:
    """Позволяет вернуть прочитанный пролог обратно в поток без чтения всего файла."""
    def __init__(self, prefix: bytes, stream: BinaryIO):
        self.prefix = prefix
        self.stream = stream
    def read(self, size: int = -1) -> bytes:
        if size is None or size < 0:
            data = self.prefix
            self.prefix = b""
            return data + self.stream.read()
        if self.prefix:
            take = self.prefix[:size]
            self.prefix = self.prefix[size:]
            if len(take) == size:
                return take
            return take + self.stream.read(size - len(take))
        return self.stream.read(size)

class Source:
    def __init__(self, path: Path):
        self.path = path
        self.zf = None
        self.stream = None
    def __enter__(self):
        if zipfile.is_zipfile(self.path):
            self.zf = zipfile.ZipFile(self.path, "r")
            candidates = [i for i in self.zf.infolist() if i.filename.lower().endswith((".xml", ".rdf"))]
            if not candidates:
                raise ValueError("В ZIP-архиве не найден XML/RDF-файл")
            if len(candidates) > 1:
                raise ValueError("В ZIP-архиве несколько XML/RDF-файлов; оставьте один или распакуйте нужный")
            self.stream = self.zf.open(candidates[0], "r")
        else:
            self.stream = self.path.open("rb")
        return self.stream
    def __exit__(self, *exc):
        if self.stream: self.stream.close()
        if self.zf: self.zf.close()

class Anonymizer:
    def __init__(self, secret: str, max_name_cache: int = 150000):
        if not secret:
            raise ValueError("Секретный ключ не может быть пустым")
        self.key = secret.encode("utf-8")
        self.namespace = uuid.UUID(bytes=hmac.new(self.key, b"cim-uuid-namespace", hashlib.sha256).digest()[:16])
        self.max_name_cache = max_name_cache
        self.name_map: dict[str, str] = {}
        self.name_map_lower: dict[str, str] = {}
        self.name_pattern = None
        self.name_overflow = False
        self.class_counts = Counter()
        self.object_count = 0

    def digest(self, value: str, purpose: str = "value") -> bytes:
        return hmac.new(self.key, (purpose + "\0" + value).encode("utf-8", "replace"), hashlib.sha256).digest()

    def token(self, value: str, purpose: str = "token", length: int = 10) -> str:
        return self.digest(value, purpose).hex()[:length].upper()

    def uuid_value(self, value: str) -> str:
        """Одинаково преобразует #_UUID, _UUID и UUID в один псевдо-UUID."""
        raw = value.strip()
        prefix = ""
        body = raw
        if body.startswith("#"):
            prefix, body = "#", body[1:]
        if body.startswith("urn:uuid:"):
            prefix, body = prefix + "urn:uuid:", body[9:]
        marker = "_" if body.startswith("_") else ""
        body = body[1:] if marker else body
        try:
            old = uuid.UUID(body.strip("{}"))
            new = uuid.uuid5(self.namespace, old.hex)
            rendered = new.hex if len(body.replace("-", "")) == 32 else str(new)
        except Exception:
            rendered = uuid.uuid5(self.namespace, body).hex
        return prefix + marker + rendered

    def numeric(self, value: str, purpose: str) -> str:
        digits = [c for c in value if c.isdigit()]
        if not digits:
            return value
        raw = self.digest(value, purpose)
        out = []
        for i in range(len(digits)):
            out.append(str(raw[i % len(raw)] % 10))
        if out and out[0] == "0": out[0] = str(1 + raw[0] % 9)
        it = iter(out)
        return "".join(next(it) if c.isdigit() else c for c in value)

    def person_name(self, value: str, purpose: str = "person") -> str:
        d = self.digest(value, purpose)
        surname = _LAST_NAMES[int.from_bytes(d[0:4], "big") % len(_LAST_NAMES)]
        first = FIRST_NAMES[int.from_bytes(d[4:8], "big") % len(FIRST_NAMES)]
        patronymic = _PATRONYMICS[int.from_bytes(d[8:12], "big") % len(_PATRONYMICS)]
        # В справочнике используются синтетические ФИО; фамилия/имя/отчество стабильны.
        return f"{surname} {first} {patronymic}"

    def synthetic_object_name(self, old: str, cls: str, identity: str = "") -> str:
        # Включение исходного ID делает новые имена уникальными даже при одинаковых старых названиях.
        d = self.digest(cls + "\0" + (identity or old), "object-name")
        adjective = ADJECTIVES[int.from_bytes(d[:4], "big") % len(ADJECTIVES)]
        prefix = CLASS_PREFIX.get(cls, cls.upper()[:18].replace("_", "-"))
        # В CIM подстанции разных назначений могут относиться к одному классу Substation.
        # Сохраняем исходное обозначение ТП/ПС/РП, если оно присутствует в названии.
        if cls == "Substation":
            match = re.search(r"(?<![А-ЯA-Z0-9])(БКТП|КТП|ЦТП|РТП|РПБ|ТП|ПС|РП)(?![А-ЯA-Z0-9])", old.upper())
            if match: prefix = match.group(1)
        elif cls == "ACLineSegment":
            match = re.search(r"(?<![А-ЯA-Z0-9])(ВЛ|КЛ|ЛЭП)(?![А-ЯA-Z0-9])", old.upper())
            if match: prefix = match.group(1)
        return f"{adjective} {prefix}-{d[4:20].hex().upper()}"

    def synthetic_org_name(self, old: str, cls: str = "Organisation", identity: str = "") -> str:
        d = self.digest(cls + "\0" + (identity or old), "org-name")
        adjective = ADJECTIVES[int.from_bytes(d[:4], "big") % len(ADJECTIVES)]
        return f"{adjective} ЭНЕРГО-{d[4:20].hex().upper()}"

    def address(self, old: str) -> str:
        d = self.digest(old, "address")
        surname = self.person_name(old, "person-fields").split()[0]
        house = 1 + int.from_bytes(d[4:6], "big") % 180
        return f"г. Синтетический, ул. {surname}, д. {house}"

    def email(self, old: str) -> str:
        n = self.person_name(old, "person-fields").lower().replace("ё", "е").split()
        return f"{n[0]}.{n[1]}@example.invalid"

    def replace_free_text(self, value: str) -> str:
        if self.name_overflow:
            # Безопасный режим для очень большого числа уникальных имён.
            value = "[ТЕКСТ ОБЕЗЛИЧЕН]"
        elif self.name_pattern is not None:
            value = self.name_pattern.sub(lambda m: self.name_map_lower.get(m.group(0).casefold(), "[ОБЪЕКТ]"), value)
        value = EMAIL_RE.sub(lambda m: self.email(m.group(0)), value)
        value = PASSPORT_RE.sub(lambda m: self.numeric(m.group(0), "passport"), value)
        value = INN_RE.sub(lambda m: self.numeric(m.group(0), "tax-id"), value)
        value = PHONE_RE.sub(lambda m: self.numeric(m.group(0), "phone"), value)
        return value

    def transform_text(self, text: Optional[str], field: str, cls: str, obj_id: str) -> Optional[str]:
        if text is None or not text.strip(): return text
        value = text
        local = field.rsplit(".", 1)[-1].lower()
        full_lower = field.lower()
        if field in PERSON_FIELDS or local in {"firstname", "lastname", "middlename", "patronymic", "fullname"}:
            full = self.person_name(obj_id or value, "person-fields")
            parts = full.split()
            if local in {"firstname"}: return parts[1]
            if local in {"lastname"}: return parts[0]
            if local in {"middlename", "patronymic"}: return parts[2]
            return full
        if "electronicaddress" in full_lower or "email" in full_lower:
            return self.email(obj_id or value)
        if "postalcode" in full_lower or "postcode" in full_lower:
            return self.numeric(value, "postal-code")
        if "streetname" in local:
            return "ул. " + self.person_name(obj_id or value, "person-fields").split()[0]
        if local in {"city", "towndetail", "town", "locality"}:
            return "Синтетический"
        if "housenumber" in local or local in {"buildingnumber", "apartmentnumber"}:
            return self.numeric(value, "house-number")
        if field in ADDRESS_FIELDS or "address" in local or "postaladdress" in full_lower:
            return self.address(obj_id or value)
        if any(x in full_lower for x in ("phone", "telephone", "mobile", "fax")):
            return self.numeric(value, "phone")
        if "fiasid" in local or "fiasstreetid" in local:
            return self.uuid_value(value)
        if any(x in local for x in ("inn", "kpp", "tax", "passport", "account", "contract", "personnel", "employee", "tabno", "serialnumber", "meteringpointcode")):
            return self.numeric(value, "identifier:" + field)
        if local in {"mrid", "mridstr"}:
            return self.uuid_value(value)
        if local in {"latitude", "longitude"}:
            try:
                number = float(value)
                offset = (int.from_bytes(self.digest(local, "geo-offset")[:4], "big") / 0xFFFFFFFF) * 30.0 + (10.0 if local == "latitude" else 20.0)
                number += offset
                if local == "latitude": number = max(-89.0, min(89.0, number))
                else: number = ((number + 180.0) % 360.0) - 180.0
                return f"{number:.8f}".rstrip("0").rstrip(".")
            except ValueError:
                return "0"
        if field == "IdentifiedObject.name":
            if cls in {"Person", "Customer"}: return self.person_name(obj_id or value, "person-name")
            if cls == "Organisation": return self.synthetic_org_name(value, cls, obj_id)
            return self.synthetic_object_name(value, cls, obj_id)
        if field == "Name.name" or field == "FolderNode.folderName" or field == "BlobStorage.name":
            return self.synthetic_object_name(value, cls, obj_id)
        if (any(x in full_lower for x in ("attachment", "blob", "filecontent", "documentcontent", "payload"))
                or (cls.lower() in {"document", "attachment", "blobstorage", "fileattachment"} and local in {"data", "content", "binary", "bytes", "filename", "filepath", "path"})):
            return "[ВЛОЖЕНИЕ ОБЕЗЛИЧЕНО]"
        if local in {"description", "comment", "comments", "note", "notes", "log", "journal", "text", "message", "markertext", "djrecordtext"}:
            return self.replace_free_text(value)
        # Не трогаем технические числовые параметры и значения бизнес-логики.
        return value

    def first_pass(self, stream: BinaryIO, db_path: Path) -> dict:
        db = sqlite3.connect(db_path)
        db.execute("PRAGMA journal_mode=WAL")
        db.execute("CREATE TABLE IF NOT EXISTS names(old TEXT PRIMARY KEY, new TEXT NOT NULL)")
        db.execute("CREATE TABLE IF NOT EXISTS ids(old_id TEXT PRIMARY KEY)")
        db.execute("DELETE FROM names")
        db.execute("DELETE FROM ids")
        counts = Counter(); objects = 0; about_count = 0; resource_count = 0
        context = etree.iterparse(stream, events=("end",), huge_tree=True, resolve_entities=False, no_network=True)
        for _, el in context:
            parent = el.getparent()
            if parent is not None and parent.tag == f"{{{RDF_NS}}}RDF":
                cls = etree.QName(el).localname
                counts[cls] += 1; objects += 1
                identity = el.get(RDF_ABOUT) or ""
                for node in el.iter():
                    about_count += int(RDF_ABOUT in node.attrib)
                    resource_count += int(RDF_RESOURCE in node.attrib)
                    old_id = node.get(RDF_ABOUT)
                    if old_id:
                        db.execute("INSERT OR IGNORE INTO ids(old_id) VALUES(?)", (old_id,))
                for child in el:
                    prop = etree.QName(child).localname
                    if not child.text or not child.text.strip():
                        continue
                    old = child.text.strip()
                    new = old
                    # Имена объектов (за исключением классификаторов, где название задаёт семантику).
                    if prop == "IdentifiedObject.name" and cls not in PRESERVE_NAME_CLASSES:
                        new = self.transform_text(old, prop, cls, identity)
                    elif prop in {"Name.name", "FolderNode.folderName", "BlobStorage.name"}:
                        new = self.transform_text(old, prop, cls, identity)
                    elif prop.startswith("Person.") and prop.rsplit(".", 1)[-1].lower() in {"firstname", "lastname", "middlename", "patronymic", "fullname"}:
                        new = self.transform_text(old, prop, cls, identity)
                    elif prop in {"Location.mainAddress", "Location.inChargeFullName", "Location.fiasId", "Location.fiasStreetId", "Asset.serialNumber", "Meter.meteringPointCode"}:
                        new = self.transform_text(old, prop, cls, identity)
                    elif any(k in prop.lower() for k in ("email", "electronicaddress", "phone", "telephone", "mobile", "fax", "postalcode", "postcode", "inn", "kpp", "tax", "passport", "account", "contract", "personnel", "employee", "tabno", "fiasid", "fiasstreetid", "latitude", "longitude")):
                        new = self.transform_text(old, prop, cls, identity)
                    if new != old:
                        db.execute("INSERT OR REPLACE INTO names(old,new) VALUES(?,?)", (old, new))
                el.clear()
                while el.getprevious() is not None: del parent[0]
                if objects % 50000 == 0:
                    db.commit(); print(f"Первичный проход: {objects:,} объектов", file=sys.stderr)
        db.commit()
        distinct = db.execute("SELECT COUNT(*) FROM names").fetchone()[0]
        unique_ids = db.execute("SELECT COUNT(*) FROM ids").fetchone()[0]
        if distinct <= min(self.max_name_cache, 250000):
            self.name_map = dict(db.execute("SELECT old,new FROM names"))
            self.name_map_lower = {k.casefold(): v for k, v in self.name_map.items() if len(k) >= 3}
            alternatives = sorted(self.name_map_lower, key=len, reverse=True)
            if alternatives:
                self.name_pattern = re.compile(r"(?i)(?:" + "|".join(re.escape(x) for x in alternatives) + r")")
        else:
            self.name_overflow = True
        db.close()
        self.class_counts = counts; self.object_count = objects
        return {"objects": objects, "classes": len(counts), "unique_names": distinct, "unique_ids": unique_ids, "class_counts": dict(counts), "rdf_about_count": about_count, "rdf_resource_count": resource_count}

    def transform_object(self, obj: etree._Element) -> None:
        cls = etree.QName(obj).localname
        about = obj.get(RDF_ABOUT)
        obj_id = about or ""
        if about:
            obj.set(RDF_ABOUT, self.uuid_value(about))
        if RDF_ID in obj.attrib:
            obj.set(RDF_ID, self.uuid_value(obj.get(RDF_ID)))
        for node in obj.iter():
            if node is obj:
                continue  # rdf:about корневого объекта уже преобразован выше.
            # Переписываем только локальные RDF-ссылки; внешние URI остаются внешними.
            for attr in list(node.attrib):
                if attr == RDF_RESOURCE:
                    ref = node.get(attr)
                    if ref and (ref.startswith("#") or ref.startswith("_")):
                        node.set(attr, self.uuid_value(ref))
                elif attr == RDF_NODEID or attr.endswith("}about") or attr.endswith("}ID"):
                    node.set(attr, self.uuid_value(node.get(attr)))
            if node.text:
                field = etree.QName(node).localname
                short = field.rsplit(".", 1)[-1].lower()
                if field.endswith(".mRID") or field.endswith(".mRIDStr"):
                    node.text = self.uuid_value(node.text)
                elif field == "IdentifiedObject.name":
                    if cls not in PRESERVE_NAME_CLASSES:
                        node.text = self.transform_text(node.text, field, cls, obj_id)
                elif field.startswith("Person.") and short in {"firstname", "lastname", "middlename", "patronymic", "fullname"}:
                    node.text = self.transform_text(node.text, field, cls, obj_id)
                elif field in {"Location.mainAddress", "Location.inChargeFullName", "Location.fiasId", "Location.fiasStreetId", "Asset.serialNumber", "Meter.meteringPointCode"}:
                    node.text = self.transform_text(node.text, field, cls, obj_id)
                elif field in {"Name.name", "FolderNode.folderName", "BlobStorage.name"}:
                    node.text = self.transform_text(node.text, field, cls, obj_id)
                elif (any(k in field.lower() for k in ("email", "electronicaddress", "phone", "telephone", "mobile", "fax", "postalcode", "postcode", "inn", "kpp", "tax", "passport", "account", "contract", "personnel", "employee", "tabno", "fiasid", "fiasstreetid", "latitude", "longitude", "comment", "description", "notes", "journal", "markertext", "djrecordtext", "attachment", "blob", "filecontent", "documentcontent", "payload", "log", "text", "message"))
                        or (cls.lower() in {"document", "attachment", "blobstorage", "fileattachment"} and short in {"content", "data", "binary", "bytes", "filename", "filepath", "path"})):
                    node.text = self.transform_text(node.text, field, cls, obj_id)
            if node.tail and self.name_overflow:
                node.tail = " "

    def second_pass(self, stream: BinaryIO, output: Path, prolog_pis: list[str], db_path: Path) -> dict:
        """Второй проход. Записывает элементы по одному и проверяет локальные RDF-ссылки."""
        counts = Counter(); objects = 0; about_count = 0; resource_count = 0
        internal_refs = 0; resolved_refs = 0; unresolved_refs = 0
        ref_db = sqlite3.connect(str(db_path))
        ref_cursor = ref_db.cursor()
        context = etree.iterparse(stream, events=("start", "end"), huge_tree=True, resolve_entities=False, no_network=True)
        root = None

        def make_ns_patterns(nsmap: dict):
            patterns = []
            for prefix, uri in nsmap.items():
                if not uri: continue
                name = b"xmlns" if prefix is None else b"xmlns:" + prefix.encode("utf-8")
                escaped = uri.replace("&", "&amp;").replace('"', "&quot;").encode("utf-8")
                patterns.append(re.compile(rb"\s" + re.escape(name) + rb"=(['\"])" + re.escape(escaped) + rb"\1"))
            return patterns

        def remove_inherited_xmlns(raw: bytes, patterns) -> bytes:
            # У дочернего CIM-объекта lxml сериализует унаследованные xmlns повторно.
            # Они уже объявлены на корне; удаляем только их из первого стартового тега.
            pos = raw.find(b">")
            if pos < 0: return raw
            head, tail = raw[:pos + 1], raw[pos + 1:]
            for pattern in patterns:
                head = pattern.sub(b"", head)
            return head + tail

        with output.open("wb") as out:
            out.write(b"<?xml version='1.0' encoding='UTF-8'?>\n")
            for pi in prolog_pis:
                try:
                    target, _, data = pi[2:-2].partition(" ")
                    pi_el = etree.ProcessingInstruction(target, data)
                    out.write(etree.tostring(pi_el, encoding="UTF-8"))
                    out.write(b"\n")
                except Exception:
                    pass
            for event, el in context:
                if event == "start" and root is None:
                    root = el
                    ns_patterns = make_ns_patterns(root.nsmap)
                    root_stub = etree.Element(root.tag, attrib=dict(root.attrib), nsmap=root.nsmap)
                    root_start = etree.tostring(root_stub, encoding="UTF-8", with_tail=False)
                    if root_start.endswith(b"/>"):
                        root_start = root_start[:-2] + b">"
                    out.write(root_start)
                    if root.text:
                        out.write(root.text.encode("utf-8"))
                elif event == "end" and root is not None and el.getparent() is root:
                    cls = etree.QName(el).localname
                    for node in el.iter():
                        about_count += int(RDF_ABOUT in node.attrib)
                        resource_count += int(RDF_RESOURCE in node.attrib)
                        ref = node.get(RDF_RESOURCE)
                        if ref and (ref.startswith("#") or ref.startswith("_")):
                            internal_refs += 1
                            if ref_cursor.execute("SELECT 1 FROM ids WHERE old_id=?", (ref,)).fetchone():
                                resolved_refs += 1
                            else:
                                unresolved_refs += 1
                    self.transform_object(el)
                    raw = etree.tostring(el, encoding="UTF-8", with_tail=True)
                    out.write(remove_inherited_xmlns(raw, ns_patterns))
                    counts[cls] += 1; objects += 1
                    el.clear()
                    while el.getprevious() is not None: del root[0]
                    if objects % 50000 == 0:
                        print(f"Обработка: {objects:,} объектов", file=sys.stderr)
            if root is not None:
                prefix = (root.prefix + ":") if root.prefix else ""
                local = etree.QName(root).localname
                out.write(f"</{prefix}{local}>".encode("utf-8"))
        ref_db.close()
        return {"objects": objects, "classes": len(counts), "class_counts": dict(counts), "rdf_about_count": about_count, "rdf_resource_count": resource_count, "internal_resource_count": internal_refs, "resolved_local_references": resolved_refs, "unresolved_local_references": unresolved_refs}


def open_source(path: Path):
    """Context manager yields (stream, prolog PIs)."""
    class _Ctx:
        def __enter__(self_nonlocal):
            self_nonlocal.src = Source(path)
            raw = self_nonlocal.src.__enter__()
            prefix = raw.read(65536)
            self_nonlocal.pis = re.findall(rb"<\?(?!xml\b)[^?]+\?>", prefix, flags=re.I)
            self_nonlocal.stream = PrefixedReader(prefix, raw)
            return self_nonlocal.stream, [x.decode("utf-8", "replace") for x in self_nonlocal.pis]
        def __exit__(self_nonlocal, *exc):
            self_nonlocal.src.__exit__(*exc)
    return _Ctx()


def main() -> int:
    ap = argparse.ArgumentParser(description="Потоковое обезличивание CIM RDF/XML")
    ap.add_argument("input", help="Исходный XML или ZIP с одним XML-файлом")
    ap.add_argument("output", help="Путь к обезличенному XML")
    ap.add_argument("--secret", default=os.environ.get("CIM_ANON_SECRET"), help="Секретный ключ; для одинакового результата между запусками используйте один и тот же ключ")
    ap.add_argument("--max-name-cache", type=int, default=200000, help="Максимум уникальных имён для точной замены упоминаний в свободном тексте")
    args = ap.parse_args()
    if not args.secret:
        ap.error("Укажите --secret или переменную окружения CIM_ANON_SECRET")
    src = Path(args.input); dst = Path(args.output)
    if not src.exists(): ap.error(f"Файл не найден: {src}")
    if src.resolve() == dst.resolve(): ap.error("Входной и выходной файлы должны различаться")
    dst.parent.mkdir(parents=True, exist_ok=True)
    anon = Anonymizer(args.secret, args.max_name_cache)
    start = time.time()
    fd, db_name = tempfile.mkstemp(prefix="cim_anon_", suffix=".sqlite3", dir=str(dst.parent))
    os.close(fd); db_path = Path(db_name)
    tmp_out = dst.with_suffix(dst.suffix + ".tmp")
    try:
        print("Этап 1/2: анализ имён и типов объектов...", file=sys.stderr)
        with open_source(src) as (stream, _):
            before = anon.first_pass(stream, db_path)
        print(f"Найдено объектов: {before['objects']:,}; классов: {before['classes']}; уникальных имён: {before['unique_names']:,}", file=sys.stderr)
        if anon.name_overflow:
            print("ВНИМАНИЕ: превышен лимит кэша имён; свободные текстовые поля будут заменяться целиком для исключения утечек.", file=sys.stderr)
        print("Этап 2/2: обезличивание и запись XML...", file=sys.stderr)
        with open_source(src) as (stream, pis):
            after = anon.second_pass(stream, tmp_out, pis, db_path)
        if (before["objects"] != after["objects"] or before["class_counts"] != after["class_counts"]
                or before["rdf_about_count"] != after["rdf_about_count"]
                or before["rdf_resource_count"] != after["rdf_resource_count"]):
            raise RuntimeError("Контроль структуры не пройден: изменилось число объектов, классов или RDF-ссылок")
        os.replace(tmp_out, dst)
        report = {
            "input": str(src), "output": str(dst), "objects": after["objects"],
            "classes": after["classes"], "class_counts": after["class_counts"],
            "rdf_about_count": after["rdf_about_count"], "rdf_resource_count": after["rdf_resource_count"],
            "unique_ids": before["unique_ids"], "internal_resource_count": after["internal_resource_count"],
            "resolved_local_references": after["resolved_local_references"],
            "unresolved_local_references": after["unresolved_local_references"],
            "unique_names": before["unique_names"], "name_cache_overflow": anon.name_overflow,
            "deterministic": True, "structure_counts_preserved": True,
            "elapsed_seconds": round(time.time() - start, 2),
        }
        report_path = dst.with_suffix(dst.suffix + ".report.json")
        report_path.write_text(json.dumps(report, ensure_ascii=False, indent=2), encoding="utf-8")
        print(f"Готово: {dst}", file=sys.stderr)
        print(f"Отчёт: {report_path}", file=sys.stderr)
        return 0
    except Exception:
        if tmp_out.exists(): tmp_out.unlink()
        raise
    finally:
        for p in (db_path, Path(str(db_path) + "-wal"), Path(str(db_path) + "-shm")):
            try: p.unlink(missing_ok=True)
            except Exception: pass

if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"ОШИБКА: {exc}", file=sys.stderr)
        raise SystemExit(2)
