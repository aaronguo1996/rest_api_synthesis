use hashbrown::HashMap;
use lasso::MiniSpur;
use serde_json::Number;
use smallvec::SmallVec;

pub type ValueIx = usize;

#[derive(Debug, Clone)]
pub enum RValue {
    // new variants for ergonomics
    Symbol(MiniSpur),
    Num(usize),

    // compat with existing
    Null,
    Bool(bool),
    String(String),
    Number(Number),
    Array(SmallVec<[ValueIx; 4]>),
    Object(HashMap<String, ValueIx>),
}

impl RValue {
    pub fn get<'r>(&'r self, key: &str, slab: &'r ThreadSlab) -> Option<(ValueIx, &'r Self)> {
        match self {
            RValue::Object(o) => o.get(key).and_then(|x| slab.get(*x).map(|v| (*x, v))),
            _ => None,
        }
    }

    pub fn is_empty(&self) -> bool {
        match self {
            RValue::Null => true,
            RValue::Object(v) => v.is_empty(),
            RValue::Array(a) => a.is_empty(),
            _ => false,
        }
    }

    pub fn as_array(&self) -> Option<&SmallVec<[ValueIx; 4]>> {
        match self {
            RValue::Array(a) => Some(a),
            _ => None,
        }
    }

    pub fn as_mut_array(&mut self) -> Option<&mut SmallVec<[ValueIx; 4]>> {
        match self {
            RValue::Array(a) => Some(a),
            _ => None,
        }
    }

    pub fn is_array(&self) -> bool {
        self.as_array().is_some()
    }

    pub fn as_symbol(&self) -> Option<MiniSpur> {
        match self {
            RValue::Symbol(s) => Some(*s),
            _ => None,
        }
    }

    pub fn as_num(&self) -> Option<usize> {
        match self {
            RValue::Num(n) => Some(*n),
            _ => None,
        }
    }

    pub fn is_num(&self) -> bool {
        self.as_num().is_some()
    }

    pub fn deep_eq<'r>(&'r self, other: &RValue, slab: &'r ThreadSlab) -> bool {
        match (self, other) {
            (RValue::Symbol(a), RValue::Symbol(b)) => a == b,
            (RValue::Num(n), RValue::Num(m)) => n == m,
            (RValue::Null, RValue::Null) => true,
            (RValue::Bool(a), RValue::Bool(b)) => a == b,
            (RValue::String(a), RValue::String(b)) => a == b,
            (RValue::Number(a), RValue::Number(b)) => a == b,
            (RValue::Array(a), RValue::Array(b)) => a
                .iter()
                .map(|x| slab.get(*x).unwrap())
                .eq_by(b.iter().map(|x| slab.get(*x).unwrap()), |a, b| {
                    a.deep_eq(b, slab)
                }),
            (RValue::Object(a), RValue::Object(b)) => a.iter().all(|(key, value)| {
                b.get(key).map_or(false, |v| {
                    slab.get(*v)
                        .and_then(|v1| slab.get(*value).map(|v2| v1.deep_eq(v2, slab)))
                        .unwrap_or(false)
                })
            }),
            _ => false,
        }
    }
}

#[derive(Debug, Default)]
pub struct RootSlab {
    pub data: Vec<RValue>,
}

impl RootSlab {
    pub fn new() -> Self {
        Self {
            data: Vec::with_capacity(500000),
        }
    }

    pub fn allocate(&mut self, v: serde_json::Value) -> ValueIx {
        use serde_json::Value;

        let r = match v {
            Value::Null => RValue::Null,
            Value::Bool(b) => RValue::Bool(b),
            Value::Number(n) => RValue::Number(n),
            Value::String(s) => RValue::String(s),
            Value::Array(a) => RValue::Array(a.into_iter().map(|x| self.allocate(x)).collect()),
            Value::Object(o) => {
                RValue::Object(o.into_iter().map(|(k, v)| (k, self.allocate(v))).collect())
            }
        };

        self.push_rval(r)
    }

    pub fn push_rval(&mut self, v: RValue) -> ValueIx {
        self.data.push(v);
        self.data.len() - 1
    }
}

pub struct ThreadSlab<'r> {
    root: &'r RootSlab,
    pub data: Vec<RValue>,
    init: usize,
}

impl<'r> ThreadSlab<'r> {
    pub fn new(root: &'r RootSlab) -> Self {
        Self {
            root,
            data: Vec::new(),
            init: root.data.len(),
        }
    }

    pub fn push_rval(&mut self, v: RValue) -> ValueIx {
        self.data.push(v);
        self.init + self.data.len() - 1
    }

    pub fn get(&self, ix: ValueIx) -> Option<&RValue> {
        if ix >= self.init {
            self.data.get(ix - self.init)
        } else {
            self.root.data.get(ix)
        }
    }

    pub fn get_mut(&mut self, ix: ValueIx) -> Option<(ValueIx, &mut RValue)> {
        if ix >= self.init {
            self.data.get_mut(ix - self.init).map(|x| (ix, x))
        } else {
            let og = self.root.data.get(ix)?;
            let new_ix = self.push_rval(og.clone());
            Some((new_ix, self.data.get_mut(new_ix - self.init).unwrap()))
        }
    }
}
