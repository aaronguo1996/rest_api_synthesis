import re
from prance import ResolvingParser, ValidationError

from openapi import defs
from openapi.preprocess import PreProcessor

def read_doc(doc_path):
    try:
        parser = ResolvingParser(doc_path)
        # spec with all the references resolved
        return parser.specification
    except ValidationError: # allow other exceptions to be thrown
        path_segs = doc_path.split('/')
        old_filename = path_segs[-1]
        name_segs = old_filename.split('.')
        new_filename = '.'.join(name_segs[:-1]) + "_preprocess.json"
        preprocessor = PreProcessor(doc_path)
        new_path = '/'.join(path_segs[:-1] + [new_filename])
        preprocessor.preprocess(new_path)
        return read_doc(new_path)

def schema_to_json(name, schema):
    if defs.DOC_PROPERTIES in schema:
        children = []
        properties = schema.get(defs.DOC_PROPERTIES)
        for k, v in properties.items():
            children.append(schema_to_json(k, v))
        return {
            "name": name,
            "children": children,
        }
    elif schema.get(defs.DOC_TYPE) == "array" and defs.DOC_ITEMS in schema:
        item_schema = schema.get(defs.DOC_ITEMS)
        children = [schema_to_json("array", item_schema)]
        return {
            "name": name,
            "children": children,
        }
    elif schema.get(defs.DOC_ONEOF):
        schemas = schema.get(defs.DOC_ONEOF)
        children = [schema_to_json(f"{name}_{i}", schema) 
            for i, schema in enumerate(schemas)]
        return {
            "name": name,
            "children": children,
        }
    else:
        return {
            "name": name,
            "value": 1,
        }

def get_schema_forest(doc):
    components = doc.get(defs.DOC_COMPONENTS)
    schemas = components.get(defs.DOC_SCHEMAS)
    schema_json = [schema_to_json(k, v) for k, v in schemas.items() 
        if not re.search("obj_ref_\d+", k)]
    return [schema for schema in schema_json 
        if isinstance(schema, dict) and "children" in schema]