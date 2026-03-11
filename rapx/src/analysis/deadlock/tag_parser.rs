use rustc_ast::token::{Token, TokenKind};
use rustc_ast::tokenstream::{TokenStream, TokenTree};
use rustc_hir::{AttrArgs, Attribute, def_id::DefId};
#[allow(unused)]
use rustc_middle::mir::{Body, Location, Statement, Terminator, TerminatorEdges, TerminatorKind};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

pub struct TagParser<'tcx> {
    tcx: TyCtxt<'tcx>,
}

#[derive(Debug)]
pub enum LockTagItem {
    LockType(
        DefId,
        String, // Name
        Span,
    ),
    LockGuardType(
        DefId,
        String, // Name
        Span,
    ),
    IntrApi(
        DefId,
        bool, // true = Enable, false = Disable
        bool, // Nested
        Span,
    ),
    IsrEntry(DefId, Span),
}

// Helper function: parse format "Name = \"SomeName\""
fn parse_name_value(tokens: &TokenStream) -> Option<String> {
    let mut iter = tokens.iter();

    // Look for pattern Name = "value"
    while let Some(tree) = iter.next() {
        if let TokenTree::Token(
            Token {
                kind: TokenKind::Ident(sym, _),
                ..
            },
            _,
        ) = tree
        {
            if sym.as_str() == "Name" {
                // Expect '='
                if let Some(TokenTree::Token(
                    Token {
                        kind: TokenKind::Eq,
                        ..
                    },
                    _,
                )) = iter.next()
                {
                    // Expect string literal
                    if let Some(TokenTree::Token(
                        Token {
                            kind: TokenKind::Literal(lit),
                            ..
                        },
                        _,
                    )) = iter.next()
                    {
                        let s = lit.symbol.as_str();
                        // Remove quotes
                        return Some(s.trim_matches('"').to_string());
                    }
                }
            }
        }
    }
    None
}

// Helper function: parse format "Type = Enable/Disable, Nested = true/false"
fn parse_intr_api(tokens: &TokenStream) -> Option<(bool, bool)> {
    let mut iter = tokens.iter();
    let mut typ_value: Option<bool> = None;
    let mut nested_value: Option<bool> = None;

    while let Some(tree) = iter.next() {
        if let TokenTree::Token(
            Token {
                kind: TokenKind::Ident(sym, _),
                ..
            },
            _,
        ) = tree
        {
            let key = sym.as_str();

            if key == "Type" {
                // Expect '='
                if let Some(TokenTree::Token(
                    Token {
                        kind: TokenKind::Eq,
                        ..
                    },
                    _,
                )) = iter.next()
                {
                    // Expect Enable or Disable
                    if let Some(TokenTree::Token(
                        Token {
                            kind: TokenKind::Ident(val_sym, _),
                            ..
                        },
                        _,
                    )) = iter.next()
                    {
                        match val_sym.as_str() {
                            "Enable" => typ_value = Some(true),
                            "Disable" => typ_value = Some(false),
                            _ => return None,
                        }
                    }
                }
            } else if key == "Nested" {
                // Expect '='
                if let Some(TokenTree::Token(
                    Token {
                        kind: TokenKind::Eq,
                        ..
                    },
                    _,
                )) = iter.next()
                {
                    // Expect true or false
                    if let Some(TokenTree::Token(
                        Token {
                            kind: TokenKind::Ident(val_sym, _),
                            ..
                        },
                        _,
                    )) = iter.next()
                    {
                        match val_sym.as_str() {
                            "true" => nested_value = Some(true),
                            "false" => nested_value = Some(false),
                            _ => return None,
                        }
                    }
                }
            }
        }
    }

    // Both values must exist
    match (typ_value, nested_value) {
        (Some(t), Some(n)) => Some((t, n)),
        _ => None,
    }
}

pub fn extract_locktag_item(did: DefId, attr: &Attribute) -> Option<LockTagItem> {
    match attr {
        Attribute::Parsed(_) => None,
        Attribute::Unparsed(box attr) => {
            let path = attr.path.segments.clone().into_vec();
            // expect at least ["rapx", "{some_attr}"]
            if path.len() < 2 {
                return None;
            };
            if path[0].as_str() != "rapx" {
                return None;
            }

            // expect delimited key-value pairs like "(Type = Enable)"
            let tokens = match &attr.args {
                AttrArgs::Delimited(delim) => delim.tokens.clone(),
                AttrArgs::Empty => {
                    if path[1].as_str() == "IsrEntry" {
                        return Some(LockTagItem::IsrEntry(did, attr.span));
                    } else {
                        return None;
                    }
                }
                _ => return None,
            };
            match path[1].as_str() {
                "LockType" => {
                    // Parse format Name = "SpinLock"
                    let name = parse_name_value(&tokens);
                    match name {
                        Some(n) => Some(LockTagItem::LockType(did, n, attr.span)),
                        None => {
                            rap_warn!("Failed to parse LockType attribute for {:?}", did);
                            None
                        }
                    }
                }
                "LockGuardType" => {
                    // Parse format Name = "SpinLockGuard"
                    let name = parse_name_value(&tokens);
                    match name {
                        Some(n) => Some(LockTagItem::LockGuardType(did, n, attr.span)),
                        None => {
                            rap_warn!("Failed to parse LockGuardType attribute for {:?}", did);
                            None
                        }
                    }
                }
                "IntrApi" => {
                    // Parse format Type = Enable/Disable, Nested = true/false
                    match parse_intr_api(&tokens) {
                        Some((typ, nested)) => {
                            Some(LockTagItem::IntrApi(did, typ, nested, attr.span))
                        }
                        None => {
                            rap_warn!("Failed to parse IntrApi attribute for {:?}", did);
                            None
                        }
                    }
                }
                _ => {
                    rap_warn!("Unsupported Lock Tag: {}", path[1].as_str());
                    None
                }
            }
        }
    }
}

impl<'tcx> TagParser<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }

    pub fn run(&self) -> Vec<LockTagItem> {
        let mut result = vec![];
        for id in self.tcx.hir_free_items() {
            let item = self.tcx.hir_item(id);
            let did = item.owner_id.def_id.to_def_id();
            let attrs = self.tcx.get_all_attrs(did);
            for attr in attrs {
                let tag_item = extract_locktag_item(did, attr);
                if let Some(item) = tag_item {
                    // rap_info!("{item:?}");
                    result.push(item);
                }
            }
        }

        let mut lock_type_count = 0;
        let mut lock_guard_type_count = 0;
        let mut intr_api_count = 0;
        let mut isr_entry_count = 0;
        for item in &result {
            match item {
                LockTagItem::LockType(..) => lock_type_count += 1,
                LockTagItem::LockGuardType(..) => lock_guard_type_count += 1,
                LockTagItem::IntrApi(..) => intr_api_count += 1,
                LockTagItem::IsrEntry(..) => isr_entry_count += 1,
            }
        }
        rap_info!(
            "Tags found: LockType = {}, LockGuardType = {}, IntrApi = {}, IsrEntry = {}",
            lock_type_count,
            lock_guard_type_count,
            intr_api_count,
            isr_entry_count
        );
        result
    }
}
