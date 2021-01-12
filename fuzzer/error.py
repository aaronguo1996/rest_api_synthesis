
class ConnectionError(Exception):
    def __init__(self, code, msg):
        self._code = code
        self._msg = msg

    def __str__(self):
        return str(self._code) + " " + self._msg


class EndpointNotFoundError(Exception):
    def __init__(self, ep, method=None):
        self._ep = ep
        self._method = method

    def __str__(self):
        if self._method:
            return f"Endpoint {self._ep} does not have method {self._method}."
        else:
            return f"Endpoint {self._ep} is not found in the documentation."

class InvalidSwaggerDoc(Exception):
    pass

class InvalidSchemaType(Exception):
    pass