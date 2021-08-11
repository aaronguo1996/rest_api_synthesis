import json

def create_bench_comp_pairs(openapi, benchmarks):
    with open(openapi, 'r') as f:
        openapi_doc = json.load(f)

    # get component names and descriptions
    comps = {}
    endpoints = openapi_doc['paths']
    for ep, ep_def in endpoints.items():
        for method, method_def in ep_def.items():
            comp_name = ep + "_" + method
            comp_desc = method_def['description']
            comps[comp_name] = comp_desc

    # get object names and descriptions
    # objs = {}
    # schemas = openapi_doc['components']['schemas']
    # for 

    with open("apiphany/benchmarks/slack_pairs.pkl", 'w') as f:
        f.write(comps)