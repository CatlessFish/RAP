use std::fmt::Display;

#[derive(Clone, Copy, Eq, PartialEq, Debug)]
pub enum DepEdge {
    Arg(usize),
    Ret,
    Fn2Lifetime,
}

impl Display for DepEdge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DepEdge::Arg(no) => write!(f, "{}", no),
            DepEdge::Ret => write!(f, "r"),
            DepEdge::Fn2Lifetime => write!(f, ""),
        }
    }
}

impl DepEdge {
    pub fn arg(no: usize) -> DepEdge {
        DepEdge::Arg(no)
    }
    pub fn ret() -> DepEdge {
        DepEdge::Ret
    }
    pub fn fn2lifetime() -> DepEdge {
        DepEdge::Fn2Lifetime
    }
}
