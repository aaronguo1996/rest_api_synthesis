use hashbrown::HashMap;
use serde_json::Value;
use smallvec::SmallVec;
use lasso::Spur;

// A group of traces is a mapping from a method, endpoint, and param names to a list of
// param values, along with the associated response value and weight.
// response value and its weight.
// TODO: SmallVec
// TODO: put Vec<Value> in key somehow - needs Hash impl for Value
pub type Traces = HashMap<(Spur, SmallVec<[Spur; 8]>), Vec<(SmallVec<[Value; 8]>, Value, usize)>>;
