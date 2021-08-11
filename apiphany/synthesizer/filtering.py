from apiphany.analyzer import dynamic
import apiphany.consts

def retrospective_execute(
    log_analyzer, entries, skip_fields, 
    re_bias_type, program):
    # print(program, flush=True)
    dynamic_analyzer = dynamic.DynamicAnalysis(
        entries,
        skip_fields,
        log_analyzer,
        abstraction_level=dynamic.CMP_ENDPOINT_AND_ARG_VALUE,
        bias_type=re_bias_type,
    )
    dynamic_analyzer.reset_env()

    # execute the program with collected traces
    return program.execute(dynamic_analyzer)

def check_results(results, multiple):
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

    # print("scores: ", scores)

    # check methods always fail
    if all_none:
        return apiphany.consts.MAX_COST

    # check multiplicity match
    score_avg = sum(scores) / len(scores)
    if ((all_singleton and multiple) or
        (all_multiple and not multiple)):
        # print("expects multiple values, but this program does not match the multiplicity")
        score_avg = score_avg + 25.0

    # penalty on all empty results
    if all_empty:
        score_avg = score_avg + 10.0

    return score_avg
