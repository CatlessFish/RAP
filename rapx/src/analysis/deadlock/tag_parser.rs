use rustc_ast::token::{Token, TokenKind};
use rustc_ast::tokenstream::{TokenStream, TokenTree};
use rustc_hir::{
    AttrArgs, Attribute,
    def_id::{CrateNum, DefId, DefIndex, LOCAL_CRATE},
};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;
use serde::{Deserialize, Serialize};

pub struct TagParser<'tcx> {
    tcx: TyCtxt<'tcx>,
}

#[derive(Debug, Clone)]
pub enum LockTagItem {
    LockType(DefId, String, SerializableSpan),
    LockGuardType(DefId, String, SerializableSpan),
    IntrApi(
        DefId,
        bool, // true = Enable, false = Disable
        bool, // Nested
        SerializableSpan,
    ),
    IsrEntry(DefId, SerializableSpan),
}

/// A stable-on-disk representation of a `DefId`.
///
/// `CrateNum` is only meaningful inside one rustc session, so the JSON cache
/// stores a logical crate identity (`crate_name`, `crate_hash`) plus the
/// per-crate `DefIndex`. During loading we resolve that logical identity back
/// to the current session's `CrateNum`.
#[derive(Debug, Serialize, Deserialize, Clone, PartialEq, Eq, Hash)]
pub struct SerializableDefId {
    pub crate_name: String,
    pub crate_hash: String,
    pub index: u32,
}

impl SerializableDefId {
    pub fn from_def_id(tcx: TyCtxt<'_>, def_id: DefId) -> Self {
        let crate_num = def_id.krate;
        SerializableDefId {
            crate_name: tcx.crate_name(crate_num).as_str().to_string(),
            crate_hash: format!("{:?}", tcx.crate_hash(crate_num)),
            index: def_id.index.as_u32(),
        }
    }

    /// Resolve the persisted crate identity in the current rustc session.
    fn resolve_crate_num(&self, tcx: TyCtxt<'_>) -> Option<CrateNum> {
        if tcx.crate_name(LOCAL_CRATE).as_str() == self.crate_name
            && format!("{:?}", tcx.crate_hash(LOCAL_CRATE)) == self.crate_hash
        {
            return Some(LOCAL_CRATE);
        }

        tcx.crates(()).iter().copied().find(|&crate_num| {
            tcx.crate_name(crate_num).as_str() == self.crate_name
                && format!("{:?}", tcx.crate_hash(crate_num)) == self.crate_hash
        })
    }

    pub fn resolve(&self, tcx: TyCtxt<'_>) -> Option<DefId> {
        self.resolve_crate_num(tcx).map(|crate_num| DefId {
            krate: crate_num,
            index: DefIndex::from_u32(self.index),
        })
    }
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct SerializableSpan {
    pub lo: u32,
    pub hi: u32,
}

impl From<Span> for SerializableSpan {
    fn from(span: Span) -> Self {
        SerializableSpan {
            lo: span.lo().0,
            hi: span.hi().0,
        }
    }
}

// Deserialized spans cannot fully recover rustc hygiene context, but they are
// still useful for diagnostics and coarse source mapping.
impl Into<Span> for SerializableSpan {
    fn into(self) -> Span {
        use rustc_span::BytePos;
        Span::with_root_ctxt(BytePos(self.lo), BytePos(self.hi))
    }
}

#[derive(Debug, Serialize, Deserialize, Clone)]
enum SerializableLockTagItem {
    LockType(SerializableDefId, String, SerializableSpan),
    LockGuardType(SerializableDefId, String, SerializableSpan),
    IntrApi(SerializableDefId, bool, bool, SerializableSpan),
    IsrEntry(SerializableDefId, SerializableSpan),
}

impl SerializableLockTagItem {
    fn from_runtime(tcx: TyCtxt<'_>, item: &LockTagItem) -> Self {
        match item {
            LockTagItem::LockType(def_id, name, span) => Self::LockType(
                SerializableDefId::from_def_id(tcx, *def_id),
                name.clone(),
                span.clone(),
            ),
            LockTagItem::LockGuardType(def_id, name, span) => Self::LockGuardType(
                SerializableDefId::from_def_id(tcx, *def_id),
                name.clone(),
                span.clone(),
            ),
            LockTagItem::IntrApi(def_id, is_enable, is_nested, span) => Self::IntrApi(
                SerializableDefId::from_def_id(tcx, *def_id),
                *is_enable,
                *is_nested,
                span.clone(),
            ),
            LockTagItem::IsrEntry(def_id, span) => {
                Self::IsrEntry(SerializableDefId::from_def_id(tcx, *def_id), span.clone())
            }
        }
    }

    fn resolve(&self, tcx: TyCtxt<'_>) -> Option<LockTagItem> {
        match self {
            Self::LockType(def_id, name, span) => def_id
                .resolve(tcx)
                .map(|did| LockTagItem::LockType(did, name.clone(), span.clone())),
            Self::LockGuardType(def_id, name, span) => def_id
                .resolve(tcx)
                .map(|did| LockTagItem::LockGuardType(did, name.clone(), span.clone())),
            Self::IntrApi(def_id, is_enable, is_nested, span) => def_id
                .resolve(tcx)
                .map(|did| LockTagItem::IntrApi(did, *is_enable, *is_nested, span.clone())),
            Self::IsrEntry(def_id, span) => def_id
                .resolve(tcx)
                .map(|did| LockTagItem::IsrEntry(did, span.clone())),
        }
    }

    fn def_id(&self) -> &SerializableDefId {
        match self {
            Self::LockType(def_id, ..)
            | Self::LockGuardType(def_id, ..)
            | Self::IntrApi(def_id, ..)
            | Self::IsrEntry(def_id, ..) => def_id,
        }
    }
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
                        return Some(LockTagItem::IsrEntry(did, attr.span.into()));
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
                        Some(n) => Some(LockTagItem::LockType(did, n, attr.span.into())),
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
                        Some(n) => Some(LockTagItem::LockGuardType(did, n, attr.span.into())),
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
                            Some(LockTagItem::IntrApi(did, typ, nested, attr.span.into()))
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

    /// Load cached tags, resolve them for the current session, analyze the local
    /// crate, and finally persist the merged cache back to disk.
    pub fn load_analyze_save(
        &self,
        load_path: Option<&str>,
        save_path: Option<&str>,
    ) -> Vec<LockTagItem> {
        let mut persisted_tags = if let Some(load_path) = load_path {
            match std::fs::read_to_string(load_path) {
                Ok(content) => match serde_json::from_str::<Vec<SerializableLockTagItem>>(&content)
                {
                    Ok(loaded) => {
                        rap_info!("Loaded {} serialized tags from {}", loaded.len(), load_path);
                        loaded
                    }
                    Err(e) => {
                        rap_warn!("Failed to parse tags from {}: {}", load_path, e);
                        vec![]
                    }
                },
                Err(e) => {
                    rap_warn!("Failed to read tag file {}: {}", load_path, e);
                    vec![]
                }
            }
        } else {
            vec![]
        };

        let mut unresolved_cached_tags = 0;
        let mut tags: Vec<LockTagItem> = persisted_tags
            .iter()
            .filter_map(|tag| match tag.resolve(self.tcx) {
                Some(tag) => Some(tag),
                None => {
                    unresolved_cached_tags += 1;
                    let def_id = tag.def_id();
                    rap_warn!(
                        "Skipping cached tag for crate {} ({}) because it is unavailable in the current session",
                        def_id.crate_name,
                        def_id.crate_hash
                    );
                    None
                }
            })
            .collect();
        if unresolved_cached_tags > 0 {
            rap_warn!(
                "Skipped {} cached tags that could not be resolved in this compilation session",
                unresolved_cached_tags
            );
        }

        let analyzed_tags = self.analyze_current_crate();
        persisted_tags.extend(
            analyzed_tags
                .iter()
                .map(|tag| SerializableLockTagItem::from_runtime(self.tcx, tag)),
        );
        tags.extend(analyzed_tags);

        if let Some(save_path) = save_path {
            match serde_json::to_string_pretty(&persisted_tags) {
                Ok(json) => {
                    if let Err(e) = std::fs::write(save_path, json) {
                        rap_warn!("Failed to save tags to {}: {}", save_path, e);
                    } else {
                        rap_info!("Saved tags to {}", save_path);
                    }
                }
                Err(e) => {
                    rap_warn!("Failed to serialize tags to JSON: {}", e);
                }
            }
        }
        tags
    }

    /// Scan current crate for tags, return tag items
    fn analyze_current_crate(&self) -> Vec<LockTagItem> {
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
