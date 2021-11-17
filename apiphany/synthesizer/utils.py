from collections import defaultdict
import consts
from openapi import defs
from schemas.types import SchemaObject, BaseType, ObjectType, UnionType, ArrayType
import math
from analyzer.utils import path_to_name

def group_types(types):
    type_dict = defaultdict(int)
    for t in types:
        type_dict[t] += 1

    return type_dict

def group_params(params):
    types = [str(p.type.ignore_array()) for p in params]
    return group_types(types)

def make_entry_name(endpoint, method):
    return endpoint + "_" + method.upper()

def make_type_transition_name(from_type, to_type):
    return consts.PREFIX_CONVERT + from_type + "_" + to_type

def is_syntactic(typ_name):
    return (
        typ_name == defs.TYPE_STRING or
        typ_name == defs.TYPE_NUM or
        typ_name == defs.TYPE_INT or
        typ_name == defs.TYPE_BOOL or
        typ_name == defs.TYPE_OBJECT
    )

TYPES_PER_ROW = 3
WRAP_LEN = 30
MULTIROW = "\\multirow{%d}{*}{%s}"
MULTICELL = "\\begin{tabular}{@{}c@{}} %s \\end{tabular}"
ROW_FMT = "%s & %s & %s & %s & %s & %s & %s \\\\\\cline{%d-7}\n"
API = "Slack"
STR_PARAM = "Parameter"
STR_RESPONSE = "Response"

def _create_annot_table(methods, entries, log_analyzer):
    def get_semantic_type(p):
        s = set([str(t.type) for t in log_analyzer.dsu.get_group(p)])
        s.add(str(p.type))
        print(s)
        return list(s)

    def wrap_terms(lst):
        build = []
        line = []
        for i, s in enumerate(lst):
            line.append(s)
            if sum([len(q) for q in line]) > WRAP_LEN:
                build.append(', '.join(line) + (',' if i < len(lst) - 1 else ''))
                line.clear()

        if len(line) > 0:
            build.append(', '.join(line))
        return "\\\\".join(build)

    class EndpointAnnot:
        def __init__(self, endpoint, parameters, responses):
            self.endpoint = endpoint
            self.parameters = parameters
            self.responses = responses
            self._prc = None
            self._rrc = None

        def total_row_count(self):
            return self.param_row_count() + self.response_row_count()

        def param_row_count(self):
            return len(self.parameters)
            # if self._prc == None:
                # self._prc = max(len(self.parameters), sum([math.ceil(len(group)/TYPES_PER_ROW) for group in self.param_semantic_types()]))
            # print("prc", self.endpoint, self._prc)
            # return self._prc

        def response_row_count(self):
            return len(self.responses)
            # if self._rrc == None:
                # self._rrc = max(len(self.responses), sum([math.ceil(len(group)/TYPES_PER_ROW) for group in self.response_semantic_types()]))
            # print("rrc", self.endpoint, self._rrc)
            # return self._rrc

        def param_semantic_types(self):
            return [get_semantic_type(p) for p in self.parameters]

        def response_semantic_types(self):
            groups = []
            for response in self.responses:
                if type(response.type) == SchemaObject:
                    group = BaseType.object_lib.get(response.type.name).aliases
                    if str(response.type) not in group:
                        group.add(str(response.type))
                    groups.append(list(group))
                else:
                    # print(self,endpoint, get_semantic_type(response))
                    groups.append(get_semantic_type(response))
            return groups

    endpoint_annots = []
    for endpoint in methods:
        e = entries.get(endpoint)
        projs = e.response.project_ad_hoc(log_analyzer)
        projs = [p.response for p in projs if
                 not isinstance(p.response.type, ObjectType) and
                 not isinstance(p.response.type, ArrayType) and
                 not isinstance(p.response.type, UnionType)
                 ]
        endpoint_annots.append(EndpointAnnot(endpoint, e.parameters, projs))

    annot_table = open("annot_table.tex", "w")
    # We want to only write the api name once and we need to know how many rows it encompasses to write the table
    write_api = True
    api_row_num = sum([annot.total_row_count() for annot in endpoint_annots])
    for endpoint_annot in endpoint_annots:
        write_endpoint = True
        write_parameter = True
        write_response = True
        endpoint_row_num = endpoint_annot.total_row_count()
        parameter_row_num = endpoint_annot.param_row_count()
        response_row_num = endpoint_annot.response_row_count()

        for i, p in enumerate(endpoint_annot.parameters):
            api_col = MULTIROW % (api_row_num, API) if write_api else " "
            endpoint_col = MULTIROW % (endpoint_row_num, endpoint_annot.endpoint) if write_endpoint else " "
            parameter_col = MULTIROW % (parameter_row_num, STR_PARAM) if write_parameter else " "
            write_api = False
            write_endpoint = False
            write_parameter = False
            name = path_to_name(p.path)
            expected_type = " " # This is to be filled out manually
            semantic_type = get_semantic_type(p)
            inferred_type = MULTICELL % (wrap_terms(semantic_type))
            required = "Yes" if p.is_required else "No"
            bline = 4
            if i == len(endpoint_annot.parameters) - 1:
                bline = 3
                if response_row_num == 0:
                    bline = 2
            row = ROW_FMT % (api_col,
                             endpoint_col,
                             parameter_col,
                             name,
                             expected_type,
                             inferred_type,
                             required,
                             bline)
            row = row.replace('_', '\\_')
            annot_table.write(row)

        for i, (response, g) in enumerate(zip(endpoint_annot.responses, endpoint_annot.response_semantic_types())):
            api_col = MULTIROW % (api_row_num, API) if write_api else " "
            endpoint_col = MULTIROW % (endpoint_row_num, endpoint_annot.endpoint) if write_endpoint else " "
            response_col = MULTIROW % (response_row_num, STR_RESPONSE) if write_response else " "
            write_api = False
            write_endpoint = False
            write_response = False
            name = response.arg_name if response.arg_name != "" else "Response"
            expected_type = " " # This is to be filled out manually
            semantic_type = g
            inferred_type = MULTICELL % (wrap_terms(semantic_type))
            required = "-"
            bline = 4
            if i == len(endpoint_annot.responses) - 1:
                bline = 2
            row = ROW_FMT % (api_col,
                             endpoint_col,
                             response_col,
                             name,
                             expected_type,
                             inferred_type,
                             required,
                             bline)
            row = row.replace('_', '\\_')
            annot_table.write(row)

        annot_table.write("\\hline")
