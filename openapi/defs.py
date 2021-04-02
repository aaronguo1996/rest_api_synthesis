# definitions of keywords in OpenAPI
DOC_PATHS = "paths"
DOC_SCHEMAS = "schemas"
DOC_SCHEMA = "schema"
DOC_TYPE = "type"
DOC_PROPERTIES = "properties"
DOC_ITEMS = "items"
DOC_DEFINITIONS = "definitions"
DOC_RESPONSES = "responses"
DOC_REF = "$ref"
DOC_COMPONENTS = "components"
DOC_LOCALREF = "#"
DOC_CONTENT = "content"
DOC_ADDITIONAL_PROP = "additionalProperties"
DOC_REQUIRED = "required"
DOC_FAKE = "_x_fake_array"
DOC_ONEOF = "oneOf"
DOC_ANYOF = "anyOf"
DOC_ALLOF = "allOf"
DOC_VERSION = "swagger"
DOC_V2 = "2.0"
DOC_PARAMS = "parameters"
DOC_NAME = "name"
DOC_ID = "id"
DOC_REQUEST = "requestBody"
DOC_OK = "ok"

# definitions of types in OpenAPI
TYPE_NONE = "none"
TYPE_ARRAY = "array"
TYPE_STRING = "string"
TYPE_INT = "integer"
TYPE_NUM = "number"
TYPE_OBJECT = "object"
TYPE_BOOL = "boolean"

# definitions of parameter type in OpenAPI
PARAM_QUERY = "query"
PARAM_HEADER = "header"
PARAM_FORM = "formData"
PARAM_BODY = "body"

# definitions of network protocol
HEADER_CONTENT = "Content-type"
HEADER_ACCEPT = "Accept"
HEADER_JSON = "application/json"
HEADER_FORM = "application/x-www-form-urlencoded"

# definitions of http method
METHOD_GET = "GET"
METHOD_POST = "POST"
METHOD_PUT = "PUT"
METHOD_DELETE = "DELETE"

# definitions of response code
CODE_OK = 200
CODE_CREATED = 201
CODE_NO_CONTENT = 204
SUCCESS_CODES = [200, 201, 204]

# definitions of annotation keys
ANN_CONSUMER = "consumer"
ANN_PRODUCER = "producer"
ANN_ENDPOINT = "endpoint"
ANN_PATH = "path"
ANN_ENUM = "enum"
ANN_COMBINE = "combine"

# other definitions
INDEX_ANY = "[?]"
UTF8 = 'utf-8'