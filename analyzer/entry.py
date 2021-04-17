from schemas.schema_type import SchemaType
from openapi import defs

class Parameter:
    def __init__(self, method, arg_name, func_name, is_required, typ, value=None):
        self.method = method
        self.arg_name = arg_name
        self.func_name = func_name
        self.value = value
        self.type = typ
        self.is_required = is_required

    def __str__(self):
        return self.__dict__

    def __repr__(self):
        return self.__str__()

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
        
class ResponseParameter(Parameter):
    def __init__(self, method, arg_name, func_name, 
        path, is_required, array_level, typ, value):
        super().__init__(method, arg_name, func_name, is_required, typ, value)
        self.path = path
        self.array_level = array_level

    def _assign_type(self, value):
        if isinstance(value, dict):
            type_dict = value.copy()
            for k in type_dict:
                type_dict[k] = self._assign_type(type_dict[k])
        elif isinstance(value, list):
            item_types = [self._assign_type(v) for v in value]
            item_type = {}
            for t in item_types:
                item_type.update(t)

            type_dict = {
                "type": "array",
                "items": item_type,
            }
        else:
            type_dict = {
                "type": "string",
            }
        
        return type_dict

    def flatten(self, path_to_defs, skip_fields):
        results = []
        aliases = {}

        if self.arg_name in skip_fields or "x-" == self.arg_name[:2]:
            return results, aliases

        if isinstance(self.value, dict):
            # print("[flatten] inferring type for", self.value)
            obj_type = SchemaType.infer_type_for(
                    path_to_defs, skip_fields, self.value)

            if (self.type is not None and 
                "unknown_obj" not in self.type.name and
                obj_type is not None and # when we know its type
                self.type.name != obj_type.name):
                aliases[self.type.name] = obj_type.name
                
            if obj_type is not None:
                if self.type is None:
                    self.type = obj_type
                else:
                    self.type.name = obj_type.name
                    self.type.schema = obj_type.schema

            if self.type is None:
                assigned_type = self._assign_type(self.value)
                self.type = SchemaType("unknown_obj", assigned_type)

            for k, v in self.value.items():
                if k in skip_fields:
                    continue

                field_schema = self.type.get_field_schema(k)
                if field_schema is None: # field not defined in the doc
                    continue

                if (self.type is not None and 
                    self.type.schema is not None and 
                    field_schema is not None):
                    typ = SchemaType(
                        self.type.name + "." + k, 
                        field_schema,
                        self.type)
                else:
                    typ = None

                p = ResponseParameter(
                    self.method, k, self.func_name,
                    self.path + [k], self.is_required, self.array_level, 
                    typ, v
                )
                fd_results, fd_aliases = p.flatten(path_to_defs, skip_fields)
                results += fd_results
                aliases.update(fd_aliases)
        elif isinstance(self.value, list):
            # infer type for each element in the array
            # if we are able to match an object type against it, 
            # we get rid of the index from the path
            # if we cannot match an object against it, 
            # leave the index as the arg name
            for i in range(len(self.value)):
                # print("[flatten] inferring type for", self.value[i])
                item_type = SchemaType.infer_type_for(
                    path_to_defs, skip_fields, self.value[i])

                if self.type is None:
                    self.type = SchemaType(
                        "unknown_list",
                        self._assign_type(self.value))
                if item_type is None:
                    item_type = SchemaType(
                        self.type.name,
                        self.type.schema.get("items"),
                        self.type.parent)
                item_type.parent = self.type.parent

                if self.type is not None and item_type.name != "unknown_obj":
                    aliases[self.type.name] = item_type.name

                p = ResponseParameter(
                    self.method, defs.INDEX_ANY, self.func_name,
                    self.path + [defs.INDEX_ANY], self.is_required,
                    self.array_level + 1,
                    item_type, self.value[i])

                it_results, it_aliases = p.flatten(path_to_defs, skip_fields)
                results += it_results
                aliases.update(it_aliases)
        else:
            if self.type is None:
                self.type = SchemaType.infer_type_for(
                    path_to_defs, skip_fields, self.value)

            # if we see a scalar value for the same type name,
            # invalidate its definition as an object
            aliases[self.type.name] = None

            return [self], aliases

        return results, aliases

    def __eq__(self, other): 
        if not isinstance(other, ResponseParameter):
            # don't attempt to compare against unrelated types
            return NotImplemented

        return (self.arg_name == other.arg_name and
                self.func_name == other.func_name and
                self.method.upper() == other.method.upper() and 
                self.path == other.path)

    def __str__(self):
        return self.arg_name + '_' + self.func_name + '_' + \
            self.method.upper() + '_' + '.'.join(self.path)

    def __hash__(self):
        return hash((
            self.arg_name,
            self.func_name,
            self.method.upper(),
            tuple(self.path)
        ))

    @staticmethod
    def from_openapi(endpoint, method, arg_name, is_required, array_level):
        return ResponseParameter(
            method, arg_name, endpoint,
            [arg_name], is_required, array_level, None, None)

class RequestParameter(Parameter):
    def __init__(self, method, arg_name, func_name, is_required, typ, value):
        super().__init__(method, arg_name, func_name, is_required, typ, value)

    def __eq__(self, other): 
        if not isinstance(other, RequestParameter):
            # don't attempt to compare against unrelated types
            return NotImplemented

        return (self.arg_name == other.arg_name and
                self.method.upper() == other.method.upper() and
                self.func_name == other.func_name)

    def __str__(self):
        return self.func_name + ':' + self.arg_name + ':' + self.method.upper()

    def __hash__(self):
        return hash((self.arg_name, self.method.upper(), self.func_name))

    @staticmethod
    def from_openapi(endpoint, method, arg_name, is_required):
        return RequestParameter(method, arg_name, endpoint, is_required, None, None)

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
    def from_openapi(skip_fields, endpoint, method, entry_def):
        """read definition from openapi and generate several entries

        Args:
            skip_fields ([type]): [description]
            endpoint ([type]): [description]
            method ([type]): [description]
            entry_def ([type]): [description]

        Returns:
            [type]: [description]
        """
        entry_params = []
        
        # read parameters
        parameters = entry_def.get(defs.DOC_PARAMS, {})
        for p in parameters:
            name = p.get(defs.DOC_NAME)
            if name in skip_fields:
                continue

            param = RequestParameter.from_openapi(
                endpoint, method, name,
                p.get(defs.DOC_REQUIRED, False))
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

            # request isn't form or json
            if request_body is None:
                return []
            
            schema = request_body.get(defs.DOC_SCHEMA)
            requires = schema.get(defs.DOC_REQUIRED, [])
            properties = schema.get(defs.DOC_PROPERTIES)

            if properties:
                for name in properties.keys():
                    if name in skip_fields:
                        continue

                    param = RequestParameter.from_openapi(
                        endpoint, method, name,
                        name in requires,
                    )
                    entry_params.append(param)

        # print("request", entry_params)

        # read responses
        responses = entry_def.get(defs.DOC_RESPONSES)
        if str(defs.CODE_OK) in responses:
            response_content = responses \
                .get(str(defs.CODE_OK)) \
                .get(defs.DOC_CONTENT)
        elif str(defs.CODE_CREATED) in responses:
            response_content = responses \
                .get(str(defs.CODE_CREATED)) \
                .get(defs.DOC_CONTENT)
        else:
            entry_response = ResponseParameter(
                method, "", endpoint, [], True, 0, None, None
            )

            return [TraceEntry(endpoint, method, entry_params, entry_response)]

        response_json = response_content.get(defs.HEADER_JSON)

        if response_json:
            response_schema = response_json.get(defs.DOC_SCHEMA)
        else:
            # non json return type
            if defs.HEADER_FORM not in response_content:
                return []
            
            response_schema = response_content \
                .get(defs.HEADER_FORM) \
                .get(defs.DOC_SCHEMA)

        requires = response_schema.get(defs.DOC_REQUIRED, [])
        response_params = response_schema.get(defs.DOC_PROPERTIES)
        if response_params is None:
            # def expand_oneof(schema):
            #     results = []
            #     if defs.DOC_ONEOF in schema:
            #         oneof_params = schema.get(defs.DOC_ONEOF)
            #         for p in oneof_params:
            #             results += expand_oneof(p)
            #     else:
            #         results.append(schema.get(defs.DOC_PROPERTIES))

            #     return results
        
            # response_params = expand_oneof(response_schema)

            # union case
            while defs.DOC_ONEOF in response_schema:
                response_schemas = response_schema.get(defs.DOC_ONEOF)
                response_schema = response_schemas[0]

            response_params = response_schema.get(defs.DOC_PROPERTIES)

            # TODO: handle array case?

        if response_params is None:
            # TODO: if the returned type is an array it enters this branch
            # does that make sense?
            entry_response = ResponseParameter(
                method, "", endpoint, [], True, 0, None, None
            )

            results = [
                TraceEntry(endpoint, method, entry_params, entry_response)
            ]
        else:
            entry_response = ResponseParameter(
                method, "", endpoint, [], True, 0,
                SchemaType(endpoint+"_response", None), None
            )

            response_param = RequestParameter(
                method, "", endpoint, True,
                SchemaType(endpoint+"_response", None), None
            )

            # this was a temporary hack to make things work
            # if endpoint == "/users/{username}":
            #     entry_response = ResponseParameter(
            #         method, "", endpoint, [], True, 0,
            #         SchemaType("ldap-mapping-user", None), None
            #     )

            results = [
                TraceEntry(endpoint, method, entry_params, entry_response)
            ]

            for name, rp in response_params.items():
                if name in skip_fields:
                    continue

                # print("name:", name)
                param = ResponseParameter.from_openapi(
                    endpoint, method, name,
                    name in requires, int(rp.get(defs.DOC_TYPE) == "array"))

                e = TraceEntry(
                    f"projection({endpoint}_response, {name})",
                    "", [response_param], param)
                results.append(e)

        return results

