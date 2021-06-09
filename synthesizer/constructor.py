import jsonref
import json

from openapi import defs
from analyzer.entry import Parameter, TraceEntry
from openapi.utils import blacklist
from schemas import types
from synthesizer.utils import make_entry_name
import consts

class Constructor:
    def __init__(self, doc, analyzer):
        self._doc = doc
        self._analyzer = analyzer

    def _create_projections(self):
        projections = {}
        objs = self._doc.get(defs.DOC_COMPONENTS).get(defs.DOC_SCHEMAS)
        for obj_name, obj_def in objs.items():
            # skip temporary types defined by ourselves
            if blacklist(obj_name):
                continue

            projection_entries = self._create_projection(obj_name, obj_def)
            projections.update(projection_entries)

        # test_entry = projections["projection(Invoice, location_id)_"]
        # print([param.type for param in test_entry.parameters])
        # print(test_entry.response.type)

        return projections

    def _create_projection(self, obj_name, obj_def):
        results = {}
        if (defs.DOC_ONEOF in obj_def or
            defs.DOC_ANYOF in obj_def or
            defs.DOC_ALLOF in obj_def):
            one_ofs = obj_def.get(defs.DOC_ONEOF, [])
            any_ofs = obj_def.get(defs.DOC_ANYOF, [])
            all_ofs = obj_def.get(defs.DOC_ALLOF, [])
            for s in one_ofs + any_ofs + all_ofs:
                projections = self._create_projection(obj_name, s)
                for name, proj in projections.items():
                    while (name in results and 
                        not results[name].same_signature(proj)):
                        name = f"{name}@"

                    results[name] = proj
        elif defs.DOC_REF in obj_def:
            ref_path = obj_def.get(defs.DOC_REF)
            typ_name = ref_path[len(consts.REF_PREFIX):]
            schema = types.get_ref_type(self._doc, typ_name)
            projections = self._create_projection(obj_name, schema)
            results.update(projections)
        elif defs.DOC_PROPERTIES in obj_def:
            properties = obj_def.get(defs.DOC_PROPERTIES)
            for name, prop in properties.items():
                # if obj_name == "Transaction" and name == "order_id":
                #     print("Find projection(Transaction, order_id)")

                typ_path = obj_name.split('.')
                if len(typ_path) > 1:
                    to_field_typ = '.'.join(typ_path[1:] + [name])
                else:
                    to_field_typ = name

                in_name = None

                parts = self._analyzer.type_partitions.get(obj_name)
                if parts is not None:
                    for i, part in enumerate(parts):
                        for p in part:
                            if to_field_typ == p[:len(to_field_typ)]:
                                in_name = f"{obj_name}_{i}"
                                break
                            if in_name is not None:
                                break
                        else:
                            in_name = None

                if in_name is None:
                    in_name = obj_name

                endpoint = f"projection({in_name}, {name})"
                proj_in = Parameter(
                    "", "obj", endpoint, ["obj"],
                    True, None, types.SchemaObject(in_name), None
                )

                is_array = prop.get(defs.DOC_TYPE) == defs.TYPE_ARRAY
                out_type = types.construct_type(f"{in_name}.{name}", prop)
                proj_out = Parameter(
                    "", "field", endpoint, ["field"],
                    True, int(is_array), out_type, None
                )
                proj_in = self._analyzer.find_same_type(proj_in)
                proj_out = self._analyzer.find_same_type(proj_out)
                entry = TraceEntry(endpoint, "", [proj_in], proj_out)
                result_key = make_entry_name(endpoint, "")
                results[result_key] = entry

                # add nested objects
                if (prop.get(defs.DOC_TYPE) == defs.TYPE_OBJECT or
                    defs.DOC_PROPERTIES in prop):
                    projections = self._create_projection(
                        f"{proj_out.type.name}.{name}", prop)
                    results.update(projections)

        return results

    
    def _create_filters(self):
        filters = {}
        objs = self._doc.get(defs.DOC_COMPONENTS).get(defs.DOC_SCHEMAS)
        for obj_name, obj_def in objs.items():
            # skip temporary types defined by ourselves
            if blacklist(obj_name):
                continue

            filter_entries = self._create_filter(obj_name, obj_name, obj_def)
            filters.update(filter_entries)

        return filters

    def _create_filter(self, obj_name, field_name, field_def):
        if field_name.count('.') > 5:
            return {}

        results = {}
        if (defs.DOC_ONEOF in field_def or
            defs.DOC_ANYOF in field_def or
            defs.DOC_ALLOF in field_def):
            one_ofs = field_def.get(defs.DOC_ONEOF, [])
            any_ofs = field_def.get(defs.DOC_ANYOF, [])
            all_ofs = field_def.get(defs.DOC_ALLOF, [])
            for s in one_ofs + any_ofs + all_ofs:
                equi_filter = self._create_filter(obj_name, field_name, s)
                for name, efilter in equi_filter.items():
                    while (name in results and 
                        not results[name].same_signature(efilter)):
                        name = f"{name}@"

                    results[name] = efilter
        elif defs.DOC_REF in field_def:
            ref_path = field_def.get(defs.DOC_REF)
            typ_name = ref_path[len(consts.REF_PREFIX):]
            schema = types.get_ref_type(self._doc, typ_name)
            if obj_name == "objs_conversation" and field_name == "objs_conversation":
                print(typ_name)
            filters = self._create_filter(obj_name, field_name, schema)
            if obj_name == "objs_conversation" and field_name == "objs_conversation":
                print(filters)
            results.update(filters)
        elif defs.DOC_PROPERTIES in field_def: # if the object has sub-fields
            properties = field_def.get(defs.DOC_PROPERTIES)
            for name, prop in properties.items():
                field_type = types.construct_type(f"{obj_name}.{name}", prop)
                # if obj_name == "objs_conversation" and name == "id":
                #     print(field_name, field_type)
                if (prop.get(defs.DOC_TYPE) == defs.TYPE_OBJECT or
                    defs.DOC_PROPERTIES in prop or
                    isinstance(field_type, types.SchemaObject)):
                    filters = self._create_filter(
                        obj_name, f"{field_name}.{name}", prop)
                    results.update(filters)
                else:
                    typ_path = field_name.split('.')
                    if len(typ_path) > 1:
                        to_field_typ = '.'.join(typ_path[1:] + [name])
                    else:
                        to_field_typ = name

                    in_name = None
                    parts = self._analyzer.type_partitions.get(obj_name)
                    opt_ins = []
                    if parts is not None:
                        for i, part in enumerate(parts):
                            if to_field_typ in part:
                                in_name = f"{obj_name}_{i}"
                                break
                            else:
                                in_name = None

                        for j in range(len(parts)):
                            if j != i:
                                param = Parameter(
                                    "", "obj", 
                                    f"filter({in_name}, {in_name}.{to_field_typ})", 
                                    ["obj"], False, None, 
                                    types.SchemaObject(f"{obj_name}_{j}"), None
                                ) 
                                opt_ins.append(param)

                        out_type = [
                            types.SchemaObject(f"{obj_name}_{j}")
                            for j in range(len(parts))
                        ]

                    if in_name is None:
                        in_name = obj_name
                        out_type = types.SchemaObject(obj_name)

                    endpoint = f"filter({in_name}, {in_name}.{to_field_typ})"
                    filter_in = [
                        Parameter(
                            "", "obj", endpoint, ["obj"], 
                            True, None, 
                            types.SchemaObject(in_name), None
                        ),
                        Parameter(
                            "", "field", endpoint, ["field"],
                            True, None, field_type, None
                        )
                    ] + opt_ins
                    filter_out = Parameter(
                        "", "obj", endpoint,
                        ["obj"], True, 1, out_type, None
                    )
                    filter_in = [self._analyzer.find_same_type(fin)
                        for fin in filter_in]
                    
                    if parts is None:
                        filter_out = self._analyzer.find_same_type(filter_out)
                        
                    entry = TraceEntry(endpoint, "", filter_in, filter_out)
                    result_key = make_entry_name(endpoint, "")
                    results[result_key] = entry
        elif obj_name != field_name:
            field_type = types.construct_type(f"{field_name}", field_def)
            endpoint = f"filter({obj_name}, {field_name})"
            filter_in = [
                Parameter(
                    "", "obj", endpoint, ["obj"], 
                    True, None, 
                    types.SchemaObject(obj_name), None
                ),
                Parameter(
                    "", "field", endpoint, ["field"],
                    True, None, field_type, None
                )
            ]
            filter_out = Parameter(
                "", "obj", endpoint,
                ["obj"], True, 1, types.SchemaObject(obj_name), None
            )
            filter_in = [self._analyzer.find_same_type(fin)
                for fin in filter_in]
            filter_out = self._analyzer.find_same_type(filter_out)
                
            entry = TraceEntry(endpoint, "", filter_in, filter_out)
            result_key = make_entry_name(endpoint, "")
            results[result_key] = entry
            
        return results


    def construct_graph(self):
        projections = self._create_projections()
        filters = self._create_filters()
        entries = dict(projections)
        entries.update(filters)
        return entries