use crate::{Arena, Expr, ExprIx, Prog, ProgIx, RootSlab, Runner, ValueIx};
use hashbrown::HashMap as HBMap;
use pyo3::{
    prelude::*,
    types::{PyList, PyType},
};
use serde_json::from_str;
use smallvec::SmallVec;
use std::{collections::HashMap, convert::TryInto};

/// `Imports` are the set of classes we need in order to translate from Python
/// to Rust.
pub struct Imports<'p> {
    pub app_expr: &'p PyAny,
    pub var_expr: &'p PyAny,
    pub projection_expr: &'p PyAny,
    pub filter_expr: &'p PyAny,
    pub equi_expr: &'p PyAny,
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
        traces: HashMap<&str, HashMap<Vec<&str>, Vec<(HashMap<&str, &PyAny>, &PyAny, usize)>>>,
        inputs: Vec<(&str, &PyAny)>,
        target_ix: ProgIx,
        multiple: bool,
        filter_num: usize,
        repeat: usize,
    ) -> PyResult<Vec<usize>> {
        // First, our imports!
        let program = PyModule::import(py, "program.program")?;

        let app_expr = program.get("AppExpr")?;
        let var_expr = program.get("VarExpr")?;
        let projection_expr = program.get("ProjectionExpr")?;
        let filter_expr = program.get("FilterExpr")?;
        let equi_expr = program.get("EquiExpr")?;
        let assign_expr = program.get("AssignExpr")?;
        let list_expr = program.get("ListExpr")?;

        let json = PyModule::import(py, "json")?;
        let dumps = json.get("dumps")?;

        let imports = Imports {
            app_expr,
            var_expr,
            projection_expr,
            filter_expr,
            equi_expr,
            assign_expr,
            list_expr,

            dumps,
        };

        // Create our arena
        let mut slab = RootSlab::new();
        let mut arena = Arena::new();

        // Then, translate our programs and traces
        let t = std::time::Instant::now();
        let progs = translate_progs(&imports, &progs, &mut arena)?;
        translate_traces(&imports, traces, &mut arena, &mut slab);
        // println!("py to rs time: {}", t.elapsed().as_micros());

        // Then, using the log analyzer, create our inputs
        let mut new_inputs = HBMap::new();

        for (input_name, input_type) in inputs {
            let vals: Vec<&PyAny> = log_analyzer
                .call_method("sample_values_by_type", (input_type,), None)?
                .extract()?;
            let vals: Vec<ValueIx> = vals
                .into_iter()
                .map(|x| jsonify(dumps, x, &mut slab))
                .collect::<PyResult<Vec<_>>>()?;

            new_inputs.insert(arena.intern_str(input_name), vals);
        }

        // Create our Runner!
        let r = Runner::new(arena, progs, new_inputs);

        let t = std::time::Instant::now();
        // And run it on our inputs
        let res = r.run(target_ix, multiple, &slab, filter_num, repeat);
        // println!("interpret time: {}", t.elapsed().as_micros());

        Ok(res)
    }

    Ok(())
}

fn jsonify(dumps: &PyAny, x: &PyAny, slab: &mut RootSlab) -> PyResult<ValueIx> {
    let json = dumps.call1((x,))?.extract()?;
    let val = from_str(json).unwrap();

    Ok(slab.allocate(val))
}

fn translate_traces<'p>(
    imports: &Imports<'p>,
    traces: HashMap<&str, HashMap<Vec<&str>, Vec<(HashMap<&str, &PyAny>, &PyAny, usize)>>>,
    arena: &mut Arena,
    slab: &mut RootSlab,
) {
    for (fun, rest) in traces.into_iter() {
        for (param_names, old_vals) in rest.into_iter() {
            let fun = arena.intern_str(&fun);
            let mut param_names = param_names
                .into_iter()
                .map(|x| arena.intern_str(&x))
                .collect::<SmallVec<_>>();
            param_names.sort();
            let mut vals = Vec::new();
            for (param_nvs, response, weight) in old_vals {
                let param_values = param_nvs
                    .into_iter()
                    .map(|(n, v)| {
                        (
                            arena.intern_str(n),
                            jsonify(imports.dumps, v, slab).unwrap(),
                        )
                    })
                    .collect::<hashbrown::HashMap<_, _>>();

                let response = jsonify(imports.dumps, response, slab).unwrap();

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
) -> PyResult<Vec<Prog>> {
    let mut res = Vec::new();

    for p in py_expr.iter() {
        let p = translate_prog(imports, p, arena)?;
        res.push(p);
    }

    Ok(res)
}

fn translate_prog<'p>(
    imports: &Imports<'p>,
    py_expr: &'p PyAny,
    arena: &mut Arena,
) -> PyResult<Prog> {
    // Simplify program first before translating!
    py_expr.call_method0("simplify")?;

    let mut inputs = SmallVec::new();
    for i in py_expr.getattr("_inputs")?.cast_as::<PyList>()?.iter() {
        inputs.push(arena.intern_str(i.extract()?));
    }

    let start = arena.get_next_prog_ix();

    for x in py_expr.getattr("_expressions")?.cast_as::<PyList>()?.iter() {
        translate_expr(imports, x, arena)?;
    }

    // Push Ret instr at end
    let end = arena.alloc_expr(Expr::Ret);

    Ok(Prog { inputs, start, end })
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
        let args = py_expr.getattr("_args")?.cast_as::<PyList>()?;

        for x in args.iter() {
            let tup = x.cast_as::<pyo3::types::PyTuple>()?;
            let name = tup.get_item(0).extract()?;
            let val = tup.get_item(1);
            translate_expr(imports, val, arena)?;
            let s = arena.intern_str(name);
            arena.alloc_expr(Expr::Push(s));
        }

        arena.alloc_expr(Expr::Push(fun));

        Ok(arena.alloc_expr(Expr::App(args.len().try_into().unwrap())))
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
        translate_expr(imports, py_expr.getattr("_obj")?, arena)?;
        // Then, intern the field
        let field = arena.intern_str(py_expr.getattr("_field")?.extract()?);
        // Finally, alloc expr
        Ok(arena.alloc_expr(Expr::Proj(field)))
    } else if imports
        .filter_expr
        .cast_as::<PyType>()
        .unwrap()
        .is_instance(py_expr)?
    {
        // Translate lhs
        translate_expr(imports, py_expr.getattr("_obj")?, arena)?;
        // Intern the field and push projection and set candidate
        let field = arena.intern_str(py_expr.getattr("_field")?.extract()?);
        arena.alloc_expr(Expr::Proj(field));
        arena.alloc_expr(Expr::SetCandidates);
        translate_expr(imports, py_expr.getattr("_val")?, arena)?;
        Ok(arena.alloc_expr(Expr::Filter))
    } else if imports
        .equi_expr
        .cast_as::<PyType>()
        .unwrap()
        .is_instance(py_expr)?
    {
        // Translate lhs
        translate_expr(imports, py_expr.getattr("_lhs")?, arena)?;
        arena.alloc_expr(Expr::SetCandidates);
        // Translate rhs
        translate_expr(imports, py_expr.getattr("_rhs")?, arena)?;
        Ok(arena.alloc_expr(Expr::Filter))
    } else if imports
        .assign_expr
        .cast_as::<PyType>()
        .unwrap()
        .is_instance(py_expr)?
    {
        // Intern the lhs, evaluate the rhs, push instr
        let lhs = arena.intern_str(py_expr.getattr("_lhs")?.extract()?);
        translate_expr(imports, py_expr.getattr("_rhs")?, arena)?;
        let bind = py_expr.getattr("_is_bind")?.extract()?;
        if bind {
            Ok(arena.alloc_expr(Expr::Bind(lhs)))
        } else {
            Ok(arena.alloc_expr(Expr::Assign(lhs)))
        }
    } else if imports
        .list_expr
        .cast_as::<PyType>()
        .unwrap()
        .is_instance(py_expr)?
    {
        // Intern the lhs, evaluate the rhs, push instr
        translate_expr(imports, py_expr.getattr("_item")?, arena)?;
        Ok(arena.alloc_expr(Expr::Singleton))
    } else {
        Err(pyo3::exceptions::PyTypeError::new_err(
            "expr not subclass of Expression",
        ))
    }
}
