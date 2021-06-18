use lasso::Spur;
use serde_json::Value;
use soa_derive::StructOfArray;

/// A `Method` is an API method.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Method {
    Get,
    Post,
    Unsupported,
}

impl std::fmt::Display for Method {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Method::Get => write!(f, "GET"),
            Method::Post => write!(f, "POST"),
            Method::Unsupported => write!(f, "HHHH"),
        }
    }
}

// TODO: try using smallvec for this and manually do the soa transform later on
/// An input parameter in a trace entry.
/// Since input parameters normally come in lists, we also do the soa transform
/// on this struct too.
#[derive(Debug)]
pub struct Param {
    pub arg_name: Spur,
    pub value: Value,
    pub required: bool,
}

pub type ParamVec = Vec<Param>;

/// A `Trace` is a trace entry.
/// We store these Traces in a struct-of-arrays fashion since normally,
/// we only care about one of the fields of each trace.
#[derive(Debug, StructOfArray)]
#[soa_derive = "Debug"]
pub struct Trace {
    pub endpoint: Spur,
    pub method: Method,
    pub params: ParamVec,
    // option to account for error responses
    pub response: Option<Value>,
}
