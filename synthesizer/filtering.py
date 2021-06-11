import random
import xeger
import pebble

from analyzer import dynamic

def retrospective_execute(
    log_analyzer, entries, skip_fields, re_bias_type, 
    inputs, program):
    dynamic_analyzer = dynamic.DynamicAnalysis(
        entries,
        skip_fields,
        abstraction_level=dynamic.CMP_ENDPOINT_AND_ARG_VALUE,
        bias_type=re_bias_type,
    )
    dynamic_analyzer.reset_env()
    
    # initialize environment with input values
    for arg_name, arg_type in inputs.items():
        vals = log_analyzer.get_values_by_type(arg_type)
        vals = list({v:v for v in vals}.keys())
        if not vals:
            # only two cases here
            if arg_type == "unit_amount_/v1/prices_POST_unit_amount":
                vals = [random.randint(1,10)]
            else:
                x = xeger.Xeger()
                vals = [x.xeger("^[a-z0-9]{10,}$")]
                
        arg_val = random.choice(vals)
        dynamic_analyzer.push_var(arg_name, arg_val)

    # execute the program with collected traces
    return program.execute(dynamic_analyzer)

def run_filter(
    log_analyzer, entries, skip_fields, re_bias_type, 
    inputs, program, multiple, repeat=5):
    print(program)

    results = []

    with pebble.ThreadPool() as pool:
        # try n times
        for _ in range(repeat):
            future = pool.schedule(
                retrospective_execute,
                args=(log_analyzer, entries, skip_fields, re_bias_type, 
                    inputs, program))
            r, score = future.result()
            print("****Program returns", r)
            results.append(future)

    results = [future.result() for future in results]

    # decide multiplicity
    all_none = True
    all_singleton = True
    all_multiple = True
    all_empty = True
    scores = []
    for result, score in results:
        if result is not None:
            if result:
                all_empty = False

            all_none = False
            while isinstance(result, list) and len(result) == 1:
                
                if len(result) == 0:
                    break

                result = result[0]

            if isinstance(result, list) and len(result) > 1:
                all_singleton = False
            else:
                all_multiple = False

            scores.append(score)

    print("scores: ", scores)

    # check methods always fail
    if all_none:
        return 999999.9

    # check multiplicity match
    score_avg = sum(scores) / len(scores)
    if all_singleton and multiple:
        print("expects multiple values, but this program does not match the multiplicity")
        score_avg = score_avg + 5.0

    if all_multiple and not multiple:
        print("expects single value, but this program does not match the multiplicity")
        score_avg = score_avg + 10.0

    # penalty on all empty results
    if all_empty:
        score_avg = score_avg + 5.0

    return score_avg
