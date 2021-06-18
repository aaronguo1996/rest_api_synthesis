use crate::{Arena, Expr, ExprIx, Method, Param, ParamVec, Prog, ProgIx, Runner, Trace};
use lasso::Spur;
use pyo3::{prelude::*, types::PyList};
use serde_json::{from_str, Value};
use smallvec::SmallVec;

/// `Imports` are the set of classes we need in order to translate from Python
/// to Rust.
pub struct Imports<'p> {
    pub app_expr: &'p PyAny,
    pub var_expr: &'p PyAny,
    pub projection_expr: &'p PyAny,
    pub filter_expr: &'p PyAny,
    pub map_expr: &'p PyAny,
    pub assign_expr: &'p PyAny,

    pub dumps: &'p PyAny,
}

#[pymodule]
pub fn apiphany(_py: Python, m: &PyModule) -> PyResult<()> {
    #[pyfn(m, "run")]
    fn run_re(
        py: Python,
        log_analyzer: &PyAny,
        progs: Vec<&PyAny>,
        traces: Vec<&PyAny>,
        inputs: Vec<(&str, &PyAny)>,
    ) -> PyResult<Vec<(ProgIx, usize)>> {
        // First, our imports!
        let program = PyModule::import(py, "program.program")?;

        let app_expr = program.get("AppExpr")?;
        let var_expr = program.get("VarExpr")?;
        let projection_expr = program.get("ProjectionExpr")?;
        let filter_expr = program.get("FilterExpr")?;
        let map_expr = program.get("MapExpr")?;
        let assign_expr = program.get("AssignExpr")?;

        let json = PyModule::import(py, "json")?;
        let dumps = json.get("dumps")?;

        let imports = Imports {
            app_expr,
            var_expr,
            projection_expr,
            filter_expr,
            map_expr,
            assign_expr,

            dumps,
        };

        // Create our arena
        let mut arena = Arena::new();

        // Then, translate our programs and traces
        let progs = translate_progs(&imports, &progs, &mut arena)?;
        translate_traces(&imports, &traces, &mut arena)?;

        // Then, using the log analyzer, create our inputs
        let mut new_inputs = Vec::new();

        for (input_name, input_type) in inputs {
            let vals: Vec<&PyAny> = log_analyzer.call_method("get_values_by_type", (input_type,), None)?.extract()?;
            let vals: Vec<Value> = vals.into_iter().map(|x| {
                let json = dumps.call1((x,))?.extract()?;
                let val = from_str(json).unwrap();

                Ok(val)
            }).collect::<PyResult<Vec<_>>>()?;

            new_inputs.push((arena.intern_str(input_name), vals));
        }

        // Create our Runner!
        let r = Runner::new(arena, progs);

        // And run it on our inputs
        let res = r.run(&new_inputs);

        Ok(res)
    }

    Ok(())
}

// TODO: translation might be slow af?
// better to parse traces ourselves...
fn translate_traces<'p>(imports: &Imports, py_expr: &[&'p PyAny], arena: &mut Arena) -> PyResult<()> {
    for t in py_expr.iter() {
        let ts = translate_trace(imports, t, arena)?;
        if ts.method != Method::Unsupported {
            arena.push_trace(ts);
        }
    }

    Ok(())
}

fn translate_progs<'p>(
    imports: &Imports<'p>,
    py_expr: &[&'p PyAny],
    arena: &mut Arena,
) -> PyResult<Vec<ProgIx>> {
    let mut res = Vec::new();

    for p in py_expr.iter() {
        let pix = translate_prog(imports, p, arena)?;
        res.push(pix);
    }

    Ok(res)
}

fn translate_trace<'p>(imports: &Imports, py_expr: &'p PyAny, arena: &mut Arena) -> PyResult<Trace> {
    let endpoint = arena.intern_str(py_expr.getattr("endpoint")?.extract()?);
    let method = match py_expr.getattr("method")?.extract()? {
        "GET" => Method::Get,
        "POST" => Method::Post,
        _ => Method::Unsupported,
    };

    // Translate parameters
    let mut params = ParamVec::new();
    for p in py_expr.getattr("parameters")?.cast_as::<PyList>()?.iter() {
        let arg_name = arena.intern_str(p.getattr("arg_name")?.extract()?);
        let required = p.getattr("is_required")?.extract()?;

        // Since the values are JSON values, but they're currently stored as Python dicts,
        // we have to dump as JSON, then turn into a JSON value with serde.
        // This isn't super performant, but since we only do this once, it should be fine
        let value: Value = from_str(imports.dumps.call1((p.getattr("value")?,))?.extract()?).unwrap();
        params.push(Param {
            arg_name,
            value,
            required,
        });
    }

    // Translate response
    let response = match py_expr.getattr("response")?.getattr("value") {
        Ok(v) => Some(from_str(imports.dumps.call1((v,))?.extract()?).unwrap()),
        Err(_) => None,
    };

    Ok(Trace {
        endpoint,
        method,
        params,
        response,
    })
}

fn translate_prog<'p>(
    imports: &Imports<'p>,
    py_expr: &'p PyAny,
    arena: &mut Arena,
) -> PyResult<ProgIx> {
    let mut inputs = SmallVec::new();
    let mut exprs = SmallVec::new();
    for i in py_expr.getattr("_inputs")?.cast_as::<PyList>()?.iter() {
        inputs.push(arena.intern_str(i.extract()?));
    }

    for x in py_expr.getattr("_expressions")?.cast_as::<PyList>()?.iter() {
        exprs.push(translate_expr(imports, x, arena)?);
    }

    Ok(arena.push_prog(Prog { inputs, exprs }))
}

fn translate_expr<'p>(
    imports: &Imports<'p>,
    py_expr: &'p PyAny,
    arena: &mut Arena,
) -> PyResult<ExprIx> {
    if imports.app_expr.get_type().is_instance(py_expr)? {
        // First, intern function
        let fun = arena.intern_str(py_expr.getattr("_fun")?.extract()?);
        // Then, translate args.
        let args = py_expr
            .getattr("_args")?
            .cast_as::<PyList>()
            .iter()
            .map(|x| {
                let tup = x.cast_as::<pyo3::types::PyTuple>()?;
                let name = tup.get_item(0).extract()?;
                let val = tup.get_item(1);
                Ok((arena.intern_str(name), translate_expr(imports, val, arena)?))
            })
            .collect::<PyResult<SmallVec<[(Spur, ExprIx); 2]>>>()?;
        Ok(arena.alloc_expr(Expr::App(fun, args)))
    } else if imports.var_expr.get_type().is_instance(py_expr)? {
        // Intern the variable and alloc the expr
        let v = arena.intern_str(py_expr.getattr("_var")?.extract()?);
        Ok(arena.alloc_expr(Expr::Var(v)))
    } else if imports.projection_expr.get_type().is_instance(py_expr)? {
        // First, translate the base expression
        let obj = translate_expr(imports, py_expr.getattr("_obj")?, arena)?;
        // Then, intern the field
        let field = arena.intern_str(py_expr.getattr("_field")?.extract()?);
        // Finally, alloc expr
        Ok(arena.alloc_expr(Expr::Proj(obj, field)))
    } else if imports.filter_expr.get_type().is_instance(py_expr)? {
        // Translate the base object and the value
        let obj = translate_expr(imports, py_expr.getattr("_obj")?, arena)?;
        let val = translate_expr(imports, py_expr.getattr("_val")?, arena)?;
        // Then intern the field and alloc expr
        let field = arena.intern_str(py_expr.getattr("_field")?.extract()?);
        Ok(arena.alloc_expr(Expr::Filter(obj, field, val)))
    } else if imports.assign_expr.get_type().is_instance(py_expr)? {
        // Intern the variable and alloc the expr
        let v = arena.intern_str(py_expr.getattr("_var")?.extract()?);
        Ok(arena.alloc_expr(Expr::Var(v)))
    } else {
        Err(pyo3::exceptions::PyTypeError::new_err(
            "expr not subclass of Expression",
        ))
    }
}
