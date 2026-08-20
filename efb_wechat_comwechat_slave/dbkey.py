"""Read WeChat SQLCipher databases from the ComWeChat slave.

The db key is stored as ``{wxid}_dbkey.json`` under each profile's
``honus.comwechat`` directory, for example::

    /data/profiles/comwechat/honus.comwechat/wxid_xxx_dbkey.json

The key file lives with the EFB profile so each container has its own named
key, instead of sharing the legacy ``db_key.json`` next to WeChat databases.
"""

from __future__ import annotations

import base64
import ctypes
import ctypes.util
import json
import logging
import os
import re
import shutil
import tempfile
import threading
from pathlib import Path
from typing import List, Optional


SQLITE_OK = 0
SQLITE_ROW = 100
SQLITE_DONE = 101
SQLITE_OPEN_READONLY = 0x00000001
SQLITE_NULL = 5
SQLITE_BLOB = 4


logger = logging.getLogger(__name__)


class DbKeyError(RuntimeError):
    """Base error for key, file, library, and query failures."""


class DbKeyUnavailable(DbKeyError):
    """The key, SQLCipher library, or requested database is unavailable."""


class DbKeyQueryError(DbKeyError):
    """SQLCipher rejected a query or failed while stepping it."""


def _is_read_only_sql(sql: Optional[str]) -> bool:
    return bool(re.match(r"^\s*select\b", str(sql or ""), re.IGNORECASE))


def resolve_database(
    db_key_json: Path,
    db_name: Optional[str] = None,
    wechat_root: Optional[os.PathLike] = None,
    wxid: Optional[str] = None,
) -> Path:
    """Return the WeChat database file for ``db_name``.

    The key file usually lives in the profile data directory, while WeChat
    databases live under ``wechat_root/<wxid>/Msg``.
    """
    name = db_name or "MicroMsg.db"
    requested = Path(name).expanduser()
    candidates: List[Path] = []

    if wechat_root is not None and wxid:
        root = Path(wechat_root).expanduser()
        msg_root = root / wxid / "Msg"
        candidates.extend((msg_root / requested, msg_root / "Multi" / requested))

    for candidate in candidates:
        if candidate.is_file():
            return candidate.resolve()

    parent = db_key_json.parent
    if requested.is_absolute():
        candidates.append(requested)
    else:
        candidates.extend((parent / requested, parent / "Multi" / requested))
    for candidate in candidates:
        if candidate.is_file():
            return candidate.resolve()

    basename = requested.name
    matches = sorted(
        (path for path in (wechat_root or parent).rglob(basename) if path.is_file()),
        key=lambda path: (len(path.relative_to(wechat_root or parent).parts), path.as_posix()),
    )
    if matches:
        return matches[0].resolve()

    raise DbKeyUnavailable("database file not found: %s" % name)


def _load_key(db_key_json: Path) -> bytes:
    try:
        payload = json.loads(db_key_json.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        raise DbKeyUnavailable("cannot read database key file: %s" % db_key_json) from exc
    key = payload.get("key") if isinstance(payload, dict) else None
    if not isinstance(key, str):
        raise DbKeyUnavailable("database key file has no key")
    try:
        value = bytes.fromhex(key.strip())
    except ValueError as exc:
        raise DbKeyUnavailable("database key is not hexadecimal") from exc
    if len(value) != 32:
        raise DbKeyUnavailable("database key must be 32 bytes")
    return value


def _library_candidates() -> List[str]:
    candidates: List[str] = []
    configured = os.environ.get("WECHATROBOT_SQLCIPHER_LIBRARY")
    if configured:
        candidates.append(configured)
    found = ctypes.util.find_library("sqlcipher")
    if found:
        candidates.append(found)
    candidates.extend(
        [
            "libsqlcipher.so.0",
            "libsqlcipher.so",
            "libsqlcipher.so.4",
            "libsqlcipher.so.3",
            "libsqlcipher.3.dylib",
            "libsqlcipher.dylib",
        ]
    )
    return list(dict.fromkeys(candidates))


def _load_sqlcipher() -> ctypes.CDLL:
    last_error: Optional[Exception] = None
    for candidate in _library_candidates():
        try:
            library = ctypes.CDLL(candidate)
            if not hasattr(library, "sqlite3_key"):
                raise OSError("sqlite3_key is missing")
            return library
        except OSError as exc:
            last_error = exc
    detail = ": %s" % last_error if last_error else ""
    raise DbKeyUnavailable("SQLCipher library is unavailable%s" % detail)


class DbKeyReader:
    """Open one WeChat database per query and never reuse a native handle."""

    def __init__(self, db_key_json: os.PathLike, library: Optional[ctypes.CDLL] = None):
        self.db_key_json = Path(db_key_json).expanduser().resolve()
        if not self.db_key_json.is_file():
            raise DbKeyUnavailable("database key file not found: %s" % self.db_key_json)
        try:
            self.db_key_json.chmod(0o600)
        except OSError:
            pass
        self.key = _load_key(self.db_key_json)
        self.library = library or _load_sqlcipher()
        self._configure_library()

    def _configure_library(self) -> None:
        library = self.library
        library.sqlite3_open_v2.argtypes = [
            ctypes.c_char_p,
            ctypes.POINTER(ctypes.c_void_p),
            ctypes.c_int,
            ctypes.c_char_p,
        ]
        library.sqlite3_open_v2.restype = ctypes.c_int
        library.sqlite3_key.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_int]
        library.sqlite3_key.restype = ctypes.c_int
        library.sqlite3_exec.argtypes = [
            ctypes.c_void_p,
            ctypes.c_char_p,
            ctypes.c_void_p,
            ctypes.c_void_p,
            ctypes.POINTER(ctypes.c_char_p),
        ]
        library.sqlite3_exec.restype = ctypes.c_int
        library.sqlite3_prepare_v2.argtypes = [
            ctypes.c_void_p,
            ctypes.c_char_p,
            ctypes.c_int,
            ctypes.POINTER(ctypes.c_void_p),
            ctypes.POINTER(ctypes.c_char_p),
        ]
        library.sqlite3_prepare_v2.restype = ctypes.c_int
        library.sqlite3_step.argtypes = [ctypes.c_void_p]
        library.sqlite3_step.restype = ctypes.c_int
        library.sqlite3_finalize.argtypes = [ctypes.c_void_p]
        library.sqlite3_finalize.restype = ctypes.c_int
        library.sqlite3_column_count.argtypes = [ctypes.c_void_p]
        library.sqlite3_column_count.restype = ctypes.c_int
        library.sqlite3_column_name.argtypes = [ctypes.c_void_p, ctypes.c_int]
        library.sqlite3_column_name.restype = ctypes.c_char_p
        library.sqlite3_column_type.argtypes = [ctypes.c_void_p, ctypes.c_int]
        library.sqlite3_column_type.restype = ctypes.c_int
        library.sqlite3_column_blob.argtypes = [ctypes.c_void_p, ctypes.c_int]
        library.sqlite3_column_blob.restype = ctypes.c_void_p
        library.sqlite3_column_bytes.argtypes = [ctypes.c_void_p, ctypes.c_int]
        library.sqlite3_column_bytes.restype = ctypes.c_int
        library.sqlite3_column_text.argtypes = [ctypes.c_void_p, ctypes.c_int]
        library.sqlite3_column_text.restype = ctypes.c_void_p
        library.sqlite3_errmsg.argtypes = [ctypes.c_void_p]
        library.sqlite3_errmsg.restype = ctypes.c_char_p
        library.sqlite3_close.argtypes = [ctypes.c_void_p]
        library.sqlite3_close.restype = ctypes.c_int
        if hasattr(library, "sqlite3_free"):
            library.sqlite3_free.argtypes = [ctypes.c_void_p]
            library.sqlite3_free.restype = None

    def _error(self, db: ctypes.c_void_p) -> str:
        message = self.library.sqlite3_errmsg(db)
        return (message or b"").decode("utf-8", "replace")

    def _exec(self, db: ctypes.c_void_p, sql: bytes) -> None:
        error = ctypes.c_char_p()
        rc = self.library.sqlite3_exec(db, sql, None, None, ctypes.byref(error))
        message = (error.value or b"").decode("utf-8", "replace")
        if error and error.value and hasattr(self.library, "sqlite3_free"):
            self.library.sqlite3_free(error)
        if rc != SQLITE_OK:
            raise DbKeyQueryError("SQLCipher setup failed (%s): %s" % (rc, message or self._error(db)))

    def _copy_snapshot(self, database: Path, destination: Path) -> Path:
        snapshot = destination / database.name
        shutil.copy2(str(database), str(snapshot))
        for suffix in ("-wal", "-shm", "-journal"):
            sidecar = database.with_name(database.name + suffix)
            if sidecar.is_file():
                shutil.copy2(str(sidecar), str(destination / sidecar.name))
        return snapshot

    def _column_value(self, statement: ctypes.c_void_p, index: int) -> str:
        library = self.library
        if library.sqlite3_column_type(statement, index) == SQLITE_NULL:
            return ""
        size = library.sqlite3_column_bytes(statement, index)
        if library.sqlite3_column_type(statement, index) == SQLITE_BLOB:
            pointer = library.sqlite3_column_blob(statement, index)
            raw = ctypes.string_at(pointer, size) if pointer and size else b""
            return base64.b64encode(raw).decode("ascii")
        pointer = library.sqlite3_column_text(statement, index)
        raw = ctypes.string_at(pointer, size) if pointer and size else b""
        return raw.decode("utf-8", "replace")

    def _query_path(self, database: Path, sql: str) -> List[List[str]]:
        library = self.library
        db = ctypes.c_void_p()
        rc = library.sqlite3_open_v2(
            os.fsencode(str(database)), ctypes.byref(db), SQLITE_OPEN_READONLY, None
        )
        if rc != SQLITE_OK:
            message = self._error(db)
            if db:
                library.sqlite3_close(db)
            raise DbKeyUnavailable("cannot open database (%s): %s" % (rc, message))

        statement = ctypes.c_void_p()
        try:
            key_buffer = ctypes.create_string_buffer(self.key)
            rc = library.sqlite3_key(db, key_buffer, len(self.key))
            if rc != SQLITE_OK:
                raise DbKeyUnavailable("SQLCipher key rejected (%s): %s" % (rc, self._error(db)))
            self._exec(
                db,
                b";".join(
                    [
                        b"PRAGMA cipher_page_size=4096",
                        b"PRAGMA kdf_iter=64000",
                        b"PRAGMA cipher_hmac_algorithm=HMAC_SHA1",
                        b"PRAGMA cipher_kdf_algorithm=PBKDF2_HMAC_SHA1",
                        b"PRAGMA query_only=ON",
                        b"PRAGMA busy_timeout=5000",
                    ]
                )
                + b";",
            )
            tail = ctypes.c_char_p()
            rc = library.sqlite3_prepare_v2(
                db, sql.encode("utf-8"), -1, ctypes.byref(statement), ctypes.byref(tail)
            )
            if rc != SQLITE_OK:
                raise DbKeyQueryError("query prepare failed (%s): %s" % (rc, self._error(db)))

            rows: List[List[str]] = []
            column_count = library.sqlite3_column_count(statement)
            headers = [
                (library.sqlite3_column_name(statement, index) or b"").decode("utf-8", "replace")
                for index in range(column_count)
            ]
            while True:
                step_rc = library.sqlite3_step(statement)
                if step_rc == SQLITE_ROW:
                    rows.append([self._column_value(statement, index) for index in range(column_count)])
                elif step_rc == SQLITE_DONE:
                    break
                else:
                    raise DbKeyQueryError("query step failed (%s): %s" % (step_rc, self._error(db)))
            return [headers] + rows if rows else []
        finally:
            if statement:
                library.sqlite3_finalize(statement)
            library.sqlite3_close(db)

    def query(
        self,
        db_name: Optional[str],
        sql: str,
        wechat_root: Optional[os.PathLike] = None,
        wxid: Optional[str] = None,
    ) -> List[List[str]]:
        database = resolve_database(self.db_key_json, db_name, wechat_root, wxid)
        with tempfile.TemporaryDirectory(prefix="wechat-dbkey-") as temporary_dir:
            snapshot = self._copy_snapshot(database, Path(temporary_dir))
            return self._query_path(snapshot, sql)


class DbKeyManager:
    """Decide when to use a profile-local db key and when to skip to native.

    The channel owns one manager.  It looks for ``{wxid}_dbkey.json`` under the
    profile data directory, or migrates the legacy ``Msg/db_key.json`` to that
    location when present.
    """

    def __init__(self, channel, data_dir: Optional[os.PathLike] = None, wechat_root: Optional[os.PathLike] = None):
        self.channel = channel
        self._lock = threading.Lock()
        self._data_dir = (
            Path(data_dir)
            if data_dir is not None
            else (
                Path(channel.data_dir)
                if hasattr(channel, "data_dir") and channel.data_dir
                else None
            )
        )
        if self._data_dir is None:
            try:
                from ehforwarderbot import utils as efb_utils

                self._data_dir = efb_utils.get_data_path(channel.channel_id)
            except Exception:
                self._data_dir = None
        self._wechat_root = Path(wechat_root) if wechat_root is not None else None
        if self._wechat_root is None:
            configured_dir = getattr(channel, "dir", None) or (channel.config or {}).get("dir")
            if configured_dir:
                self._wechat_root = Path(str(configured_dir).rstrip("/\\"))
            else:
                self._wechat_root = Path(getattr(channel, "base_path", "."))
        self._key_path: Optional[Path] = None
        self._reader: Optional[DbKeyReader] = None

    def _candidate_key_path(self, wxid: str) -> Path:
        return Path(self._data_dir) / f"{wxid}_dbkey.json"

    def _legacy_key_path(self, wxid: Optional[str]) -> Optional[Path]:
        if not wxid or self._wechat_root is None:
            return None
        path = Path(self._wechat_root) / wxid / "Msg" / "db_key.json"
        return path if path.is_file() else None

    def _migrate_legacy_key(self, wxid: str) -> Path:
        legacy = self._legacy_key_path(wxid)
        candidate = self._candidate_key_path(wxid)
        if legacy is None:
            return candidate
        try:
            if not candidate.is_file():
                Path(self._data_dir).mkdir(parents=True, exist_ok=True)
                shutil.copy2(str(legacy), str(candidate))
                try:
                    candidate.chmod(0o600)
                except OSError:
                    pass
                logger.warning("Migrated WeChat db key to %s", candidate)
            return candidate
        except OSError:
            return legacy

    def _discover_key_path(self) -> Optional[Path]:
        if self._data_dir is None:
            return None
        wxid = getattr(self.channel, "wxid", None)
        if not wxid:
            return None
        candidate = self._candidate_key_path(wxid)
        if candidate.is_file():
            return candidate
        migrated = self._migrate_legacy_key(wxid)
        return migrated if migrated.is_file() else None

    def _get_reader(self) -> Optional[DbKeyReader]:
        key_path = self._discover_key_path()
        if key_path is None:
            return None
        with self._lock:
            if self._key_path != key_path or self._reader is None:
                self._reader = DbKeyReader(key_path)
                self._key_path = key_path
            return self._reader

    def _invalidate_reader(self) -> None:
        with self._lock:
            self._key_path = None
            self._reader = None

    def query(self, db_name: Optional[str], sql: Optional[str]) -> Optional[dict]:
        """Return a dbkey response, or None when the caller should use native."""
        if not db_name or not sql or not _is_read_only_sql(sql):
            return None
        try:
            reader = self._get_reader()
            if reader is None:
                return None
            return {
                "result": "OK",
                "data": reader.query(
                    db_name,
                    sql,
                    wechat_root=self._wechat_root,
                    wxid=getattr(self.channel, "wxid", None),
                ),
            }
        except Exception as exc:
            self._invalidate_reader()
            logger.warning(
                "WeChat dbkey query failed (%s), falling back to native: %r",
                db_name,
                exc,
            )
            return None
