from analyzer.traces import typeChecker
from analyzer.openapi import defs

class Parameter:
    def __init__(self, method, arg_name, func_name, value):
        self.method = method
        self.arg_name = arg_name
        self.func_name = func_name
        self.value = value

    def __str__(self):
        return self.__dict__

    def __repr__(self):
        return self.__str__()

class ResponseParameter(Parameter):
    def __init__(self, method, arg_name, func_name, path, value):
        super().__init__(method, arg_name, func_name, value)
        self.path = path

    def flatten(self, path_to_defs, skip_fields):
        results = []

        if self.arg_name in skip_fields:
            return results

        if isinstance(self.value, dict):
            for k, v in self.value.items():
                p = ResponseParameter(
                    self.method, k, self.func_name,
                    self.path + [k], v)
                results += p.flatten(path_to_defs, skip_fields)
        elif isinstance(self.value, list):
            #TODO: infer type for each element in the array
            # if we are able to match an object type against it, we get rid of the index from the path
            # if we cannot match an object against it, leave the index as the arg name
            for i in range(len(self.value)):
                p = None
                obj_defs = typeChecker.Type.get_object_def(path_to_defs)
                for obj_name, obj in obj_defs.items():
                    obj_type = typeChecker.Type(obj_name, obj)
                    if obj_type.is_type_of(self.value[i]):
                        # print("find object for", self.value[i], "is", obj_type.schema["title"])
                        p = ResponseParameter(
                            self.method, defs.INDEX_ANY, self.func_name,
                            self.path + [defs.INDEX_ANY], self.value[i])
                        break
                
                if not p:
                    p = ResponseParameter(
                        self.method, defs.INDEX_ANY, self.func_name,
                        self.path + [defs.INDEX_ANY], self.value[i])
                
                results += p.flatten(path_to_defs, skip_fields)
        else:
            return [self]

        return results

    def path_to_str(self, rep):
        ind = [p for p in self.path if p == defs.INDEX_ANY]
        cnt = len(ind)
        return cnt, "[" * cnt + rep + "]" * cnt

    def __eq__(self, other): 
        if not isinstance(other, ResponseParameter):
            # don't attempt to compare against unrelated types
            return NotImplemented

        return (self.arg_name == other.arg_name and
                self.func_name == other.func_name and
                self.method.upper() == other.method.upper() and 
                self.path == other.path)

    def __str__(self):
        return self.arg_name + '_' + self.func_name + '_' + self.method.upper() + '_' + '.'.join(self.path)

    def __hash__(self):
        return hash((self.arg_name, self.func_name, self.method.upper(), tuple(self.path)))

class RequestParameter(Parameter):
    def __init__(self, method, arg_name, func_name, value):
        super().__init__(method, arg_name, func_name, value)

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

class LogEntry:
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
                ",".join(resp_strs))