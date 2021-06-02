def find_expr(exprs, expr):
    for e, v in exprs:
        if e == expr:
            return v

    return None