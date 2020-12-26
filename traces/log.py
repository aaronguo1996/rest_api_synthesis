class Parameter:
    def __init__(self, arg_name, value):
        self.arg_name = arg_name
        self.value = value

class ResponseParameter(Parameter):
    def __init__(self, arg_name, path, value):
        super().__init__(arg_name, value)
        self.path = path

    def flatten(self):
        if isinstance(self.value, dict):
            results = []
            for k, v in self.value.items():
                p = ResponseParameter(k, self.path + [k], v)
                results += p.flatten()
            return results
        else:
            return [self]

class RequestParameter(Parameter):
    def __init__(self, arg_name, func_name, value):
        super().__init__(arg_name, value)
        self.func_name = func_name

class LogEntry:
    def __init__(self, endpoint, method, parameters, responses):
        self.endpoint = endpoint
        self.method = method
        self.parameters = parameters
        self.response = responses