import re
import copy
import random

from openapi import defs
from analyzer.entry import Parameter, TraceEntry
from openapi.utils import blacklist
from schemas import types
from synthesizer.utils import make_entry_name, make_type_transition_name, make_partial_trans_name
import consts
from analyzer.utils import get_representative

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

            projection_entries = self._create_projection(obj_name, obj_name, obj_def)
            projections.update(projection_entries)

        # test_entry = projections["projection(Invoice, location_id)_"]
        # print([param.type for param in test_entry.parameters])
        # print(test_entry.response.type)

        return projections

    def _create_projection(self, obj_name, field_name, obj_def):
        results = {}
        if (defs.DOC_ONEOF in obj_def or
            defs.DOC_ANYOF in obj_def or
            defs.DOC_ALLOF in obj_def):
            one_ofs = obj_def.get(defs.DOC_ONEOF, [])
            any_ofs = obj_def.get(defs.DOC_ANYOF, [])
            all_ofs = obj_def.get(defs.DOC_ALLOF, [])
            for s in one_ofs + any_ofs + all_ofs:
                projections = self._create_projection(obj_name, field_name, s)
                for name, proj in projections.items():
                    while (name in results and
                        not results[name].same_signature(proj)):
                        name = f"{name}@"

                    results[name] = proj
        elif defs.DOC_REF in obj_def:
            ref_path = obj_def.get(defs.DOC_REF)
            typ_name = ref_path[len(consts.REF_PREFIX):]
            schema = types.get_ref_type(self._doc, typ_name)
            projections = self._create_projection(obj_name, field_name, schema)
            results.update(projections)
        elif (defs.DOC_ITEMS in obj_def and
            obj_def.get(defs.DOC_TYPE) == defs.TYPE_ARRAY):
            schema = obj_def.get(defs.DOC_ITEMS)
            projections = self._create_projection(obj_name, field_name, schema)
            results.update(projections)
        elif defs.DOC_PROPERTIES in obj_def:
            properties = obj_def.get(defs.DOC_PROPERTIES)
            for name, prop in properties.items():
                typ_path = obj_name.split('.')
                if len(typ_path) > 1:
                    to_field_typ = '.'.join(typ_path[1:] + [name])
                else:
                    to_field_typ = name

                
                in_name = obj_name
                if '{' in in_name and '}' in in_name:
                    in_typ = types.construct_type(field_name, obj_def)
                else:
                    if types.BaseType.object_lib.get(in_name) is None:
                        return results

                    in_typ = types.SchemaObject(in_name)

                endpoint = f"projection({in_name}, {name})"
                proj_in = Parameter(
                    "", "obj", endpoint, ["obj"], True, None, in_typ, None
                )

                is_array = prop.get(defs.DOC_TYPE) == defs.TYPE_ARRAY
                out_type = types.construct_type(f"{field_name}.{name}", prop)

                # skip uninformative fields
                if (isinstance(out_type, types.ObjectType) and
                    not out_type.object_fields):
                    continue

                proj_out = Parameter(
                    "", "field", endpoint, ["field"], True, int(is_array), out_type, None
                )
                proj_in = self._analyzer.find_same_type(proj_in)
                proj_out = self._analyzer.find_same_type(proj_out)
                entry = TraceEntry(endpoint, "", None, [proj_in], proj_out)
                result_key = make_entry_name(endpoint, "")
                results[result_key] = entry

                # add nested objects
                if (defs.DOC_PROPERTIES in prop or (
                        prop.get(defs.DOC_TYPE) == defs.TYPE_ARRAY and
                        defs.DOC_ITEMS in prop
                    )):
                    out_type = proj_out.type.ignore_array()
                    out_name = str(out_type)
                    if isinstance(out_type, types.ObjectType):
                        out_field = f"{field_name}.{name}"
                    else:
                        out_field = out_name

                    projections = self._create_projection(
                        out_name, out_field, prop)
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
            filters = self._create_filter(obj_name, field_name, schema)
            results.update(filters)
        elif (defs.DOC_ITEMS in field_def and
            field_def.get(defs.DOC_TYPE) == defs.TYPE_ARRAY):
            schema = field_def.get(defs.DOC_ITEMS)
            filters = self._create_filter(
                obj_name,
                f"{field_name}.{defs.INDEX_ANY}",
                schema)
            results.update(filters)
        elif defs.DOC_PROPERTIES in field_def: # if the object has sub-fields
            properties = field_def.get(defs.DOC_PROPERTIES)
            for name, prop in properties.items():
                field_type = types.construct_type(f"{field_name}.{name}", prop)
                # skip uninformative fields
                if (isinstance(field_type, types.ObjectType) and
                    not field_type.object_fields):
                    continue

                if (defs.DOC_PROPERTIES in prop or
                    isinstance(field_type, types.SchemaObject) or (
                        prop.get(defs.DOC_TYPE) == defs.TYPE_ARRAY and
                        defs.DOC_ITEMS in prop
                    )):
                    filters = self._create_filter(
                        obj_name, f"{field_name}.{name}", prop)
                    results.update(filters)
                else:
                    typ_path = field_name.split('.')
                    if len(typ_path) > 1:
                        to_field_typ = '.'.join(typ_path[1:] + [name])
                    else:
                        to_field_typ = name

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
                    ]
                    filter_out = Parameter(
                        "", "obj", endpoint,
                        ["obj"], True, 1, out_type, None
                    )
                    filter_in = [self._analyzer.find_same_type(fin)
                        for fin in filter_in]

                    entry = TraceEntry(endpoint, "", None, filter_in, filter_out)
                    result_key = make_entry_name(endpoint, "")
                    results[result_key] = entry
        elif obj_name != field_name:
            field_type = types.construct_type(f"{field_name}", field_def)
            # skip uninformative fields
            if (isinstance(field_type, types.ObjectType) and
                not field_type.object_fields):
                return results

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

            entry = TraceEntry(endpoint, "", None, filter_in, filter_out)
            result_key = make_entry_name(endpoint, "")
            results[result_key] = entry

        return results

    def _construct_type_trans(self, projections):
        results = {}

        # for all semantic types, transition to its syntactic type
        semantic_types = {}

        # semantic types appear in the union-find results
        groups = self._analyzer.dsu.groups()
        for group in groups:
            rep = get_representative(group)
            if rep is not None:
                param = random.choice(list(group))
                while param.type is None or param.type.name is None:
                    param = random.choice(list(group))
                    
                semantic_types[rep] = param

        # semantic types appear in the projections (this should subsumes those in filters)
        for proj in projections.values():
            for param in proj.parameters + [proj.response]:
                if param.type.name is not None:
                    semantic_types[param.type.name] = param

        for name, param in semantic_types.items():
            if (self._analyzer._uncovered_opt != consts.UncoveredOption.EXCLUDE and (
                name != defs.TYPE_BOOL and
                name != defs.TYPE_INT and
                name != defs.TYPE_STRING and
                name != defs.TYPE_NUM and
                name != defs.TYPE_OBJECT)):
                prim_name = param.type.get_primitive_name()
                out_type = copy.deepcopy(param.type)
                out_type = out_type.to_syntactic()

                trans_name = make_type_transition_name(name, prim_name)
                results[trans_name] = TraceEntry(
                    trans_name, "", None,
                    [Parameter("", "in", trans_name, ["in"], True, None, 
                        param.type, None)],
                    Parameter("", "out", trans_name, ["out"], True, None,
                        out_type, None)
                )

        return results

    def _create_partial_trans(self, projections):
        results = {}
        for f, entry in projections.items():
            match = re.search(r"projection\((.*), (.*)\)_", f)
            obj_name = match.group(1)
            field_name = match.group(2)
            # reverse the filters to construct complete objects from partial fields
            trans_name = make_partial_trans_name(obj_name, field_name)
            params = [Parameter("", field_name, trans_name, [field_name], True, None, entry.response.type, None)]
            response = entry.parameters[0]
            results[trans_name] = TraceEntry(trans_name, "", None, params, response)

        return results

    def construct_graph(self, with_syntactic=False, with_partials=False):
        projections = self._create_projections()
        filters = self._create_filters()
        
        entries = dict(projections)
        entries.update(filters)

        if with_syntactic:
            transitions = self._construct_type_trans(projections)
            entries.update(transitions)

        if with_partials:
            partials = self._create_partial_trans(projections)
            entries.update(partials)
            
        return entries