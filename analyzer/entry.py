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

        if self.arg_name in skip_fields:
            return results

        # if self.func_name == "/conversations.info":
        #     print(f"conversations.info has arg {self.arg_name} of response type", self.type)

        if isinstance(self.value, dict):
            if (defs.DOC_OK not in self.value and 
                (not self.type or self.type.name[:11] == "unknown_obj")): # when we don't know its type
                self.type = SchemaType.infer_type_for(
                    path_to_defs, skip_fields, self.value)

                # if self.func_name == "/pins.list":
                #     print(f"pins.list has arg {self.arg_name} of response type", self.type)
                    # print("type schema is", self.type.schema)
            # if self.arg_name == "response_metadata":
            #     print(self.type.name)

            if not self.type and defs.DOC_OK not in self.value:
                # print(f"assigning type for {self.value}")
                assigned_type = self._assign_type(self.value)
                self.type = SchemaType("unknown_obj", assigned_type)

            for k, v in self.value.items():
                if k in skip_fields:
                    continue

                if (self.type and self.type.schema and 
                    self.type.get_field_schema(k)):
                    typ = SchemaType(
                        self.type.name + "." + k, 
                        self.type.get_field_schema(k),
                        self.type)
                else:
                    # if self.func_name == "/chat.postMessage" and self.type and not self.type.get_field_schema(k):
                    #     print(f"{v} is not found in type {self.type.name}")
                    typ = None

                p = ResponseParameter(
                    self.method, k, self.func_name,
                    self.path + [k], self.is_required, self.array_level, 
                    typ, v
                )
                results += p.flatten(path_to_defs, skip_fields)
        elif isinstance(self.value, list):
            # infer type for each element in the array
            # if we are able to match an object type against it, 
            # we get rid of the index from the path
            # if we cannot match an object against it, 
            # leave the index as the arg name
            for i in range(len(self.value)):
                item_type = SchemaType.infer_type_for(
                    path_to_defs, skip_fields, self.value[i])

                if not item_type:
                    self.type = SchemaType(
                        "unknown_list", 
                        self._assign_type(self.value))
                    item_type = SchemaType(
                        "unknown_obj", 
                        self.type.schema.get("items"))
                
                p = ResponseParameter(
                    self.method, defs.INDEX_ANY, self.func_name,
                    self.path + [defs.INDEX_ANY], self.is_required, 
                    self.array_level + 1,
                    item_type, self.value[i])

                results += p.flatten(path_to_defs, skip_fields)
        else:
            # if self.func_name == "/pins.list":
            #     print(f"pins.list has arg {self.arg_name} of response type", self.type)
            if self.type is None:
                self.type = SchemaType.infer_type_for(
                    path_to_defs, skip_fields, self.value)
            return [self]

        return results

    # def path_to_str(self, rep):
    #     return 0, rep
    #     # ind = [p for p in self.path if p == defs.INDEX_ANY]
    #     # cnt = len(ind)
    #     # return cnt, "[" * cnt + rep + "]" * cnt

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

class DocEntry:
    def __init__(self, endpoint, method, parameters, responses):
        self.endpoint = endpoint
        self.method = method
        self.parameters = parameters
        self.responses = responses

    def __str__(self):
        param_strs = map(str, self.parameters)
        resp_strs = map(str, self.responses)
        return (self.method.upper() + " " + self.endpoint + "\n" +
                ",".join(param_strs) + "\n" + 
                ",".join(resp_strs) + "\n")
    
    def __repr__(self):
        return self.__str__()

    def __eq__(self, other):
        if not isinstance(other, DocEntry):
            return NotImplemented

        return (self.endpoint == other.endpoint and
            self.method == other.method and
            self.parameters == other.parameters and
            self.responses == other.responses)

    @staticmethod
    def from_openapi(skip_fields, endpoint, method, entry_def):
        entry_params = []
        
        # read parameters
        parameters = entry_def.get(defs.DOC_PARAMS)
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
        if request_params:
            request_body = request_params \
                .get(defs.DOC_CONTENT) \
                .get(defs.HEADER_FORM)
            if request_body is None:
                request_body = request_params \
                    .get(defs.DOC_CONTENT) \
                    .get(defs.HEADER_JSON)
            
            schema = request_body.get(defs.DOC_SCHEMA)
            requires = schema.get(defs.DOC_REQUIRED, [])
            properties = schema.get(defs.DOC_PROPERTIES)

            for name in properties.keys():
                if name in skip_fields:
                    continue

                param = RequestParameter.from_openapi(
                    endpoint, method, name,
                    name in requires,
                )
                entry_params.append(param)

        entry_responses = []
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

        requires = response_schema.get(defs.DOC_REQUIRED, [])
        response_params = response_schema.get(defs.DOC_PROPERTIES)
        # TODO: this is specific to Slack API, should modify this to fit other domains
        for name, rp in response_params.items():
            if name in skip_fields:
                continue

            # skip requires for test
            # if name not in requires:
            #     continue

            param = ResponseParameter.from_openapi(
                endpoint, method, name,
                name in requires, int(rp.get(defs.DOC_TYPE) == "array"))
            entry_responses.append(param)

        return DocEntry(endpoint, method, entry_params, entry_responses)