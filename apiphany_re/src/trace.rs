use lasso::Spur;
use serde_json::Value;
use soa_derive::StructOfArray;

/// A `Method` is an API method.
#[derive(Debug, Copy, Clone)]
pub enum Method {
    Get,
    Put,
}

// TODO: try using smallvec for this and manually do the soa transform later on
/// An input parameter in a trace entry.
/// Since input parameters normally come in lists, we also do the soa transform
/// on this struct too.
#[derive(Debug, StructOfArray)]
#[soa_derive = "Debug"]
pub struct Param {
    arg_name: Spur,
    value: Value,
    required: bool,
}

/// A `Trace` is a trace entry.
/// We store these Traces in a struct-of-arrays fashion since normally,
/// we only care about one of the fields of each trace.
#[derive(Debug, StructOfArray)]
#[soa_derive = "Debug"]
pub struct Trace {
    endpoint: Spur,
    method: Method,
    parameters: ParamVec,
    // option to account for error responses
    response: Option<Value>,
}
