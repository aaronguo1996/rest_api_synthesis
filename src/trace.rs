use hashbrown::HashMap;
use serde_json::Value;
use smallvec::SmallVec;
use lasso::MiniSpur;

// A group of traces is a mapping from a method, endpoint, and param names to a list of
// param values, along with the associated response value and weight.
// response value and its weight.
pub type Traces = HashMap<(MiniSpur, SmallVec<[MiniSpur; 8]>), Vec<(HashMap<MiniSpur, Value>, Value, usize)>>;
