from analyzer.utils import ignore_arg_name, make_response_name
from collections import defaultdict
import re

from openapi import defs
from schemas import types

class ErrorResponse:
    def __init__(self, msg):
        self._error_msg = msg

    def __str__(self):
        return f"error: {self._error_msg}"

    def __repr__(self):
        return self.__str__()

    def __eq__(self, other):
        if isinstance(other, ErrorResponse):
            return NotImplemented

        return self._error_msg == other._error_msg
        
class Parameter:
    def __init__(self, method, arg_name, func_name, 
        path, is_required, array_level, typ, value):
        self.method = method
        self.arg_name = arg_name
        self.func_name = func_name
        self.value = value
        self.type = typ
        self.is_required = is_required
        self.path = path
        self.array_level = array_level

    def _flatten_object(self, path_to_defs, skip_fields):
        results = []
        values = defaultdict(list)

        try:
            # store the value into a mapping
            if self.type is not None and self.type.name is not None:
                # if re.search(r"^.*_response$", self.type.name):
                #     return [self], values

                values[self.type.name].append(self.value)
            
            for k, v in self.value.items():
                if k in skip_fields:
                    continue

                field_schema, is_required = self.type.get_object_field(k)                
                if field_schema is None: # field not defined in the doc
                    continue

                p = Parameter(
                    self.method, k, self.func_name,
                    self.path + [k],
                    is_required and self.is_required,
                    self.array_level, 
                    field_schema, v
                )
                fd_results, fd_values = p.flatten(path_to_defs, skip_fields)
                results += fd_results
                for t in fd_values:
                    values[t] += fd_values[t]

        except:
            raise Exception(self.method, self.func_name, self.path, self.is_required, self.value, self.type)
        
        return results, values

    def _flatten_array(self, path_to_defs, skip_fields):
        results = []
        values = defaultdict(list)

        for i in range(len(self.value)):
            if self.type is not None and self.type.name is not None:
                values[self.type.name].append(self.value)

            if self.array_level is None:
                array_level = None
            else:
                array_level = self.array_level + 1

            try:
                item_type = self.type.get_item()
                p = Parameter(
                    self.method, defs.INDEX_ANY, self.func_name,
                    self.path + [defs.INDEX_ANY], self.is_required,
                    array_level, item_type, self.value[i])
            except:
                raise Exception(self.method, self.func_name, self.path, self.is_required, self.value)

            it_results, it_values = p.flatten(path_to_defs, skip_fields)
            results += it_results
            for t in it_values:
                values[t] += it_values[t]

        return results, values

    def flatten(self, path_to_defs, skip_fields):
        if ignore_arg_name(skip_fields, self.arg_name):
            return [], {}

        if isinstance(self.value, dict):
            return self._flatten_object(path_to_defs, skip_fields)
        elif isinstance(self.value, list):
            return self._flatten_array(path_to_defs, skip_fields)
        else:
            return [self], {}

    def flatten_ad_hoc(self, skip_fields):
        results = []
        
        if ignore_arg_name(skip_fields, self.arg_name):
            return results

        if self.type is not None:
            if isinstance(self.type, types.ObjectType):
                fields = self.type.object_fields
                for field, field_typ in fields.items():
                    value = None if self.value is None else self.value[field]
                    is_required = (
                        self.is_required and 
                        field in self.type.required_fields)
                    p = Parameter(
                        self.method, field, self.func_name,
                        self.path + [field], is_required,
                        self.array_level, field_typ, value)
                    results += p.flatten_ad_hoc(skip_fields)
            elif isinstance(self.type, types.ArrayType):
                item_type = self.type.item
                value = None if self.value is None else self.value[0]
                array_level = None if self.array_level is None \
                    else self.array_level + 1
                p = Parameter(
                    self.method, defs.INDEX_ANY, self.func_name,
                    self.path + [defs.INDEX_ANY], self.is_required,
                    array_level, item_type, value
                )
                results += p.flatten_ad_hoc(skip_fields)
            elif isinstance(self.type, types.UnionType):
                items = self.type.items
                p = Parameter(
                    self.method, self.arg_name, self.func_name,
                    self.path, self.is_required, self.array_level,
                    items[0], self.value # TODO: is this sufficient?
                )
                results += p.flatten_ad_hoc(skip_fields)
            else:
                results.append(self)
        else:
            results.append(self)

        return results

    def project_ad_hoc(self, analyzer):
        projections = []
        if isinstance(self.type, types.ObjectType):
            fields = self.type.object_fields
            for field, field_typ in fields.items():
                proj_name = f"projection({self.type}, {field})"
                field_path = self.path + [field]
                p = Parameter(
                    "",         # method
                    field,      # arg name
                    proj_name,  # func name
                    field_path, # path
                    True,       # is required
                    0,          # array level
                    field_typ,
                    None,
                )
                proj_field = TraceEntry(
                    proj_name,
                    "",
                    [analyzer.set_type(self)],
                    analyzer.set_type(p)
                )
                projections.append(proj_field)
                projections += p.project_ad_hoc(analyzer)
        elif isinstance(self.type, types.ArrayType):
            p = Parameter(
                "",
                self.arg_name, 
                self.func_name,
                self.path,
                True,
                self.array_level + 1,
                self.type.item,
                None,
            )
            projections += p.project_ad_hoc(analyzer)
        elif isinstance(self.type, types.UnionType):
            for t in self.type.items:
                p = Parameter(
                    "",
                    self.arg_name,
                    self.func_name,
                    self.path,
                    True,
                    self.array_level,
                    t,
                    None,
                )
                projections += p.project_ad_hoc(analyzer)

        return projections

    def __eq__(self, other): 
        if not isinstance(other, Parameter):
            # don't attempt to compare against unrelated types
            return NotImplemented

        same_array_level = (
            (self.array_level is None and other.array_level is None) or
            (self.array_level is not None and other.array_level is not None)
        )

        return (self.arg_name == other.arg_name and
                self.func_name == other.func_name and
                self.method.upper() == other.method.upper() and
                same_array_level and
                self.path == other.path)

    def __str__(self):
        return self.arg_name + '_' + self.func_name + '_' + \
            self.method.upper() + '_' + '.'.join(self.path)

    def __repr__(self):
        return self.__str__()

    def __hash__(self):
        return hash((
            self.arg_name,
            self.func_name,
            self.method.upper(),
            tuple(self.path)
        ))

    @staticmethod
    def from_openapi(endpoint, method, arg_name, 
        type_def, is_required, array_level):
        # pass definition here and construct a type for it
        typ = types.construct_type(None, type_def)
        return Parameter(
            method, arg_name, endpoint,
            [arg_name], is_required, array_level, typ, None)

class TraceEntry:
    def __init__(self, endpoint, method, parameters, response):
        self.endpoint = endpoint
        self.method = method
        self.parameters = parameters
        self.response = response

    def __str__(self):
        param_strs = map(str, self.parameters)
        return (self.method.upper() + " " + self.endpoint + "\n" +
                ",".join(param_strs) + "\n" + str(self.response))

    def __repr__(self):
        return self.__str__()

    def __eq__(self, other):
        if not isinstance(other, TraceEntry):
            return NotImplemented

        return (self.endpoint == other.endpoint and
            self.method == other.method and
            self.parameters == other.parameters and
            self.response == other.response)

    @staticmethod
    def from_openapi_params(endpoint, method, entry_def):
        entry_params = []
        
        # read parameters
        parameters = entry_def.get(defs.DOC_PARAMS, {})
        for p in parameters:
            name = p.get(defs.DOC_NAME)
            if name == defs.DOC_TOKEN:
                continue

            param = Parameter.from_openapi(
                endpoint, method, name,
                p.get(defs.DOC_SCHEMA),
                p.get(defs.DOC_REQUIRED, False), None)
            entry_params.append(param)

        # read request body
        request_params = entry_def.get(defs.DOC_REQUEST)
        if request_params is not None:
            request_body = request_params \
                .get(defs.DOC_CONTENT) \
                .get(defs.HEADER_FORM)
            if request_body is None:
                request_body = request_params \
                    .get(defs.DOC_CONTENT) \
                    .get(defs.HEADER_JSON)
            
            if request_body is not None:
                schema = request_body.get(defs.DOC_SCHEMA)
                requires = schema.get(defs.DOC_REQUIRED, [])
                properties = schema.get(defs.DOC_PROPERTIES)

                for name, typ_def in properties.items():
                    if name == defs.DOC_TOKEN:
                        continue

                    param = Parameter.from_openapi(
                        endpoint, method, name, typ_def,
                        name in requires, None,
                    )
                    entry_params.append(param)
        
        return entry_params

    @staticmethod
    def from_openapi(endpoint, method, entry_def):
        """read definition from openapi and generate several entries
        """
        entry_params = TraceEntry.from_openapi_params(
            endpoint, method, entry_def)

        # read responses
        responses = entry_def.get(defs.DOC_RESPONSES)
        response_content = responses \
            .get(str(defs.CODE_OK)) \
            .get(defs.DOC_CONTENT)
        response_json = response_content.get(defs.HEADER_JSON)

        if response_json:
            response_schema = response_json.get(defs.DOC_SCHEMA)
        else:
            response_schema = response_content \
                .get(defs.HEADER_FORM) \
                .get(defs.DOC_SCHEMA)

        # response_name = make_response_name(endpoint, method)
        response_typ = types.construct_type(None, response_schema)
        entry_response = Parameter(
            method, "", endpoint, [], True, 
            int(response_schema.get(defs.DOC_TYPE) == defs.TYPE_ARRAY), 
            response_typ, None
        )

        return TraceEntry(endpoint, method, entry_params, entry_response)

    
