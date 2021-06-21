use crate::{Arena, Expr, ExprIx, Prog, ProgIx, Runner};
use std::collections::HashMap;
use lasso::Spur;
use pyo3::{
    prelude::*,
    types::{PyList, PyType},
};
use serde_json::{from_str, Value};
use smallvec::SmallVec;

/// `Imports` are the set of classes we need in order to translate from Python
/// to Rust.
pub struct Imports<'p> {
    pub app_expr: &'p PyAny,
    pub var_expr: &'p PyAny,
    pub projection_expr: &'p PyAny,
    pub filter_expr: &'p PyAny,
    pub assign_expr: &'p PyAny,
    pub list_expr: &'p PyAny,

    pub dumps: &'p PyAny,
}

#[pymodule]
pub fn apiphany(_py: Python, m: &PyModule) -> PyResult<()> {
    #[pyfn(m, "rust_re")]
    fn rust_re(
        py: Python,
        log_analyzer: &PyAny,
        progs: Vec<&PyAny>,
        // traces: fun -> param_names -> param_val map, response, weight
        traces: HashMap<String, HashMap<Vec<String>, Vec<(HashMap<String, &PyAny>, &PyAny, usize)>>>,
        inputs: Vec<(&str, &PyAny)>,
    ) -> PyResult<Vec<(ProgIx, usize)>> {
        // First, our imports!
        let program = PyModule::import(py, "program.program")?;

        let app_expr = program.get("AppExpr")?;
        let var_expr = program.get("VarExpr")?;
        let projection_expr = program.get("ProjectionExpr")?;
        let filter_expr = program.get("FilterExpr")?;
        let assign_expr = program.get("AssignExpr")?;
        let list_expr = program.get("ListExpr")?;

        let json = PyModule::import(py, "json")?;
        let dumps = json.get("dumps")?;

        let imports = Imports {
            app_expr,
            var_expr,
            projection_expr,
            filter_expr,
            assign_expr,
            list_expr,

            dumps,
        };

        // Create our arena
        let mut arena = Arena::new();

        // Then, translate our programs and traces
        let t = std::time::Instant::now();
        let progs = translate_progs(&imports, &progs, &mut arena)?;
        translate_traces(&imports, traces, &mut arena);
        println!("py to rs time: {}", t.elapsed().as_micros());

        // Then, using the log analyzer, create our inputs
        let mut new_inputs = Vec::new();

        for (input_name, input_type) in inputs {
            let vals: Vec<&PyAny> = log_analyzer
                .call_method("get_values_by_type", (input_type,), None)?
                .extract()?;
            let vals: Vec<Value> = vals
                .into_iter()
                .map(|x| jsonify(dumps, x))
                .collect::<PyResult<Vec<_>>>()?;

            new_inputs.push((arena.intern_str(input_name), vals));
        }

        // Create our Runner!
        let r = Runner::new(arena, progs);

        let t = std::time::Instant::now();
        // And run it on our inputs
        let res = r.run(&new_inputs);
        println!("interpret time: {}", t.elapsed().as_micros());

        Ok(res)
    }

    Ok(())
}

fn jsonify(dumps: &PyAny, x: &PyAny) -> PyResult<Value> {
    let json = dumps.call1((x,))?.extract()?;
    let val = from_str(json).unwrap();

    Ok(val)
}

fn translate_traces<'p>(
    imports: &Imports<'p>,
    traces: HashMap<String, HashMap<Vec<String>, Vec<(HashMap<String, &PyAny>, &PyAny, usize)>>>,
    arena: &mut Arena,
) {
    for (fun, rest) in traces.into_iter() {
        for (mut param_names, old_vals) in rest.into_iter() {
            let fun = arena.intern_str(&fun);
            param_names.sort();
            let param_names = param_names.into_iter().map(|x| arena.intern_str(&x)).collect::<SmallVec<_>>();
            let mut vals = Vec::new();
            for (param_nvs, response, weight) in old_vals {
                let param_values = {
                    let mut i = param_nvs
                        .into_iter()
                        .map(|(n, v)| (n, jsonify(imports.dumps, v).unwrap()))
                        .collect::<Vec<_>>();
                    i.sort_by(|x, y| x.0.cmp(&y.0));

                    i.into_iter().map(|x| x.1).collect()
                };

                let response = jsonify(imports.dumps, response).unwrap();

                vals.push((param_values, response, weight));
            }
            arena.push_trace(fun, param_names, vals)
        }
    }
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

fn translate_prog<'p>(
    imports: &Imports<'p>,
    py_expr: &'p PyAny,
    arena: &mut Arena,
) -> PyResult<ProgIx> {
    // Simplify program first before translating!
    py_expr.call_method0("simplify")?;

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
    if imports
        .app_expr
        .cast_as::<pyo3::types::PyType>()
        .unwrap()
        .is_instance(py_expr)?
    {
        // First, intern function
        let fun = arena.intern_str(py_expr.getattr("_fun")?.extract()?);
        // Then, translate args.
        let args = py_expr
            .getattr("_args")?
            .cast_as::<PyList>()?
            .iter()
            .map(|x| {
                let tup = x.cast_as::<pyo3::types::PyTuple>()?;
                let name = tup.get_item(0).extract()?;
                let val = tup.get_item(1);
                Ok((arena.intern_str(name), translate_expr(imports, val, arena)?))
            })
            .collect::<PyResult<SmallVec<[(Spur, ExprIx); 2]>>>()?;
        Ok(arena.alloc_expr(Expr::App(fun, args)))
    } else if imports
        .var_expr
        .cast_as::<PyType>()
        .unwrap()
        .is_instance(py_expr)?
    {
        // Intern the variable and alloc the expr
        let v = arena.intern_str(py_expr.getattr("_var")?.extract()?);
        Ok(arena.alloc_expr(Expr::Var(v)))
    } else if imports
        .projection_expr
        .cast_as::<PyType>()
        .unwrap()
        .is_instance(py_expr)?
    {
        // First, translate the base expression
        let obj = translate_expr(imports, py_expr.getattr("_obj")?, arena)?;
        // Then, intern the field
        let field = arena.intern_str(py_expr.getattr("_field")?.extract()?);
        // Finally, alloc expr
        Ok(arena.alloc_expr(Expr::Proj(obj, field)))
    } else if imports
        .filter_expr
        .cast_as::<PyType>()
        .unwrap()
        .is_instance(py_expr)?
    {
        // Translate the base object and the value
        let obj = translate_expr(imports, py_expr.getattr("_obj")?, arena)?;
        let val = translate_expr(imports, py_expr.getattr("_val")?, arena)?;
        // Then intern the field and alloc expr
        let field = arena.intern_str(py_expr.getattr("_field")?.extract()?);
        Ok(arena.alloc_expr(Expr::Filter(obj, field, val)))
    } else if imports
        .assign_expr
        .cast_as::<PyType>()
        .unwrap()
        .is_instance(py_expr)?
    {
        // Intern the lhs, evaluate the rhs, push instr
        let lhs = arena.intern_str(py_expr.getattr("_lhs")?.extract()?);
        let rhs = translate_expr(imports, py_expr.getattr("_rhs")?, arena)?;
        let bind = py_expr.getattr("_is_bind")?.extract()?;
        Ok(arena.alloc_expr(Expr::Assign(lhs, rhs, bind)))
    } else if imports
        .list_expr
        .cast_as::<PyType>()
        .unwrap()
        .is_instance(py_expr)?
    {
        // Intern the lhs, evaluate the rhs, push instr
        let item = translate_expr(imports, py_expr.getattr("_item")?, arena)?;
        Ok(arena.alloc_expr(Expr::Singleton(item)))
    } else {
        Err(pyo3::exceptions::PyTypeError::new_err(
            "expr not subclass of Expression",
        ))
    }
}
