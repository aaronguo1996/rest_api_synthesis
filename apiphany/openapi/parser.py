from urllib.parse import urlparse

from apiphany.schemas import types
from apiphany.openapi import defs
from apiphany.analyzer.entry import TraceEntry

class OpenAPIParser:
    def __init__(self, doc):
        self._doc = doc

    def parse(self):
        self._construct_object_lib()
        hostname, base_path = self._parse_server()
        entries = self._construct_entries()
        return hostname, base_path, entries

    def _construct_object_lib(self):
        # get all schemas
        schemas = self._doc.get(defs.DOC_COMPONENTS).get(defs.DOC_SCHEMAS)
        for name, schema in schemas.items():
            typ = types.construct_type(name, schema)
            types.BaseType.object_lib[name] = typ

    def _construct_entries(self):
        entries = {}
        # get all paths
        paths = self._doc.get(defs.DOC_PATHS)
        for path, path_def in paths.items():
            entries[path] = {}
            for method, path_method_def in path_def.items():
                method = method.upper()
                entry = TraceEntry.from_openapi(
                    self._doc, path, method, path_method_def)
                entries[path][method] = entry

        return entries

    def _parse_server(self):
        # strip out the hostname part and get the real endpoint
        servers = self._doc.get(defs.DOC_SERVERS)
        server = servers[0].get(defs.DOC_URL)
        server_result = urlparse(server)
        hostname = server_result.netloc
        base_path = server_result.path
        return hostname, base_path