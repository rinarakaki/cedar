use std::{
    collections::{BTreeMap, HashMap},
    str::FromStr,
};

use cedar_policy_core::ast::{Id, Name};
use combine::{
    between, choice, eof, error::StreamError, many, many1, optional, satisfy_map, sep_by1,
    stream::ResetStream, ParseError, Parser, Positioned, StreamOnce,
};
use itertools::Itertools;
use logos::{Logos, Span};
use smol_str::SmolStr;
use thiserror::Error;

use crate::{
    ActionEntityUID, ActionType, ApplySpec, AttributesOrContext, EntityType, NamespaceDefinition,
    SchemaFragment, SchemaType, SchemaTypeVariant, TypeOfAttribute,
};

// Cedar tokens
#[derive(Logos, Clone, Debug, PartialEq)]
enum Token {
    #[regex(r"\s*", logos::skip)]
    Whitespace,
    #[regex(r"//[^\n\r]*[\n\r]*", logos::skip)]
    Comment,
    #[regex(r"[_a-zA-Z][_a-zA-Z0-9]*", |lex| SmolStr::new(lex.slice()))]
    Identifier(SmolStr),
    #[regex(r#""(\\.|[^"\\])*""#, |lex| SmolStr::new(lex.slice()))]
    Str(SmolStr),
    // PRIMTYPE  := 'Long' | 'String' | 'Bool'
    #[token("Long")]
    TyLong,
    #[token("String")]
    TyString,
    #[token("Bool")]
    TyBool,
    // VAR := 'principal' | 'action' | 'resource' | 'context'
    #[token("principal")]
    VarPrincipal,
    #[token("action")]
    VarAction,
    #[token("resource")]
    VarResource,
    #[token("context")]
    VarContext,
    #[token("entity")]
    Entity,
    #[token("in")]
    In,
    #[token("type")]
    Type,
    #[token("Set")]
    Set,
    #[token("appliesTo")]
    AppliesTo,
    #[token("namespace")]
    Namespace,
    #[token(",")]
    Comma,
    #[token(";")]
    SemiColon,
    #[token(":")]
    Colon,
    #[token("::")]
    DoubleColon,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token("[")]
    LBracket,
    #[token("]")]
    RBracket,
    #[token("<")]
    LAngle,
    #[token(">")]
    RAngle,
    #[token("\"")]
    Quote,
    #[token("=")]
    Eq,
    #[token("?")]
    Question,
}

#[derive(Debug, Clone, PartialEq, Error)]
pub enum ParseErrors {
    #[error("Lexer error: {0}")]
    Lexing(SmolStr),
    #[error("Expecting: {0}")]
    Expected(SmolStr),
    #[error("Unexpected: {0}")]
    Unexpected(SmolStr),
    #[error("Parser error: {0}")]
    Message(SmolStr),
    #[error("End of input")]
    Eoi,
    #[error("Other error: {0}")]
    Other(SmolStr),
}

impl<'a> StreamError<(Token, Span), &'a [(Token, Span)]> for ParseErrors {
    fn unexpected_token(token: (Token, Span)) -> Self {
        Self::Unexpected(SmolStr::new(format!("{token:?}")))
    }
    fn unexpected_range(tokens: &'a [(Token, Span)]) -> Self {
        Self::Unexpected(SmolStr::new(format!("{tokens:?}")))
    }
    fn unexpected_format<T>(msg: T) -> Self
    where
        T: std::fmt::Display,
    {
        Self::Unexpected(SmolStr::new(msg.to_string()))
    }
    fn expected_token(token: (Token, Span)) -> Self {
        Self::Expected(SmolStr::new(format!("{token:?}")))
    }
    fn expected_range(tokens: &'a [(Token, Span)]) -> Self {
        Self::Expected(SmolStr::new(format!("{tokens:?}")))
    }
    fn expected_format<T>(msg: T) -> Self
    where
        T: std::fmt::Display,
    {
        Self::Expected(SmolStr::new(msg.to_string()))
    }
    fn message_token(token: (Token, Span)) -> Self {
        Self::Message(SmolStr::new(format!("{token:?}")))
    }
    fn message_range(tokens: &'a [(Token, Span)]) -> Self {
        Self::Message(SmolStr::new(format!("{tokens:?}")))
    }
    fn message_format<T>(msg: T) -> Self
    where
        T: std::fmt::Display,
    {
        Self::Message(SmolStr::new(msg.to_string()))
    }
    fn is_unexpected_end_of_input(&self) -> bool {
        match self {
            Self::Eoi => true,
            _ => false,
        }
    }
    fn into_other<T>(self) -> T
    where
        T: StreamError<(Token, Span), &'a [(Token, Span)]>,
    {
        match self {
            Self::Lexing(s) => T::message_format(s),
            Self::Eoi => T::end_of_input(),
            Self::Expected(s) => T::expected_format(s),
            Self::Message(s) => T::message_format(s),
            Self::Unexpected(s) => T::unexpected_format(s),
            Self::Other(s) => T::message_format(s),
        }
    }
}

impl<'a> ParseError<(Token, Span), &'a [(Token, Span)], ()> for ParseErrors {
    type StreamError = Self;
    fn empty(_position: ()) -> Self {
        Self::Eoi
    }
    fn set_position(&mut self, _position: ()) {
        unimplemented!("set_position")
    }
    fn add(&mut self, err: Self::StreamError) {
        *self = err;
    }
    fn set_expected<F>(_self_: &mut combine::error::Tracked<Self>, _info: Self::StreamError, _f: F)
    where
        F: FnOnce(&mut combine::error::Tracked<Self>),
    {
        unimplemented!("set_expected")
    }
    fn is_unexpected_end_of_input(&self) -> bool {
        StreamError::is_unexpected_end_of_input(self)
    }
    fn into_other<T>(self) -> T
    where
        T: ParseError<(Token, Span), &'a [(Token, Span)], ()>,
    {
        unimplemented!("into_other")
    }
}

#[derive(Debug, Clone)]
struct TokenStream<'a> {
    pub token_spans: &'a [(Token, Span)],
}

impl<'a> StreamOnce for TokenStream<'a> {
    type Error = ParseErrors;
    type Position = ();
    type Token = (Token, Span);
    type Range = &'a [(Token, Span)];

    fn uncons(&mut self) -> Result<Self::Token, combine::stream::StreamErrorFor<Self>> {
        match &self.token_spans[..] {
            [] => Err(ParseErrors::Eoi),
            _ => {
                let (f, r) = self.token_spans.split_first().unwrap();
                self.token_spans = r;
                Ok(f.clone())
            }
        }
    }
}

impl<'a> ResetStream for TokenStream<'a> {
    type Checkpoint = Self;
    fn checkpoint(&self) -> Self::Checkpoint {
        self.clone()
    }
    fn reset(&mut self, checkpoint: Self::Checkpoint) -> Result<(), Self::Error> {
        *self = checkpoint;
        Ok(())
    }
}

impl<'a> Positioned for TokenStream<'a> {
    fn position(&self) -> Self::Position {
        ()
    }
}

fn parse_id<'a>() -> impl Parser<TokenStream<'a>, Output = Id> {
    satisfy_map(|ts| match ts {
        (Token::Identifier(d), _) => Some(Id::from_str(&d).unwrap()),
        _ => None,
    })
}

fn parse_ids<'a>() -> impl Parser<TokenStream<'a>, Output = Vec<Id>> {
    sep_by1(parse_id(), accept(Token::Comma))
}

fn accept<'a>(t: Token) -> impl Parser<TokenStream<'a>, Output = ()> {
    satisfy_map(move |tt: (Token, Span)| if tt.0 == t { Some(()) } else { None })
}

struct AppParser();

impl<'a> Parser<TokenStream<'a>> for AppParser {
    type Output = ApplySpec;
    type PartialState = ();
    fn parse_lazy(
        &mut self,
        input: &mut TokenStream<'a>,
    ) -> combine::ParseResult<Self::Output, <TokenStream<'a> as combine::StreamOnce>::Error> {
        match self.parse(input.clone()) {
            Ok((res, tokens)) => {
                *input = tokens;
                combine::ParseResult::CommitOk(res)
            }
            Err(err) => combine::ParseResult::PeekErr(combine::error::Tracked::from(err)),
        }
    }

    // AppDecls  := VAR ':' EntOrTyps [',' | ',' AppDecls]
    fn parse(
        &mut self,
        input: TokenStream<'a>,
    ) -> Result<(Self::Output, TokenStream<'a>), <TokenStream<'a> as combine::StreamOnce>::Error>
    {
        (
            choice((
                (
                    accept(Token::VarContext),
                    accept(Token::Colon),
                    parse_rec_type(),
                )
                    .map(|(_, _, rec)| ApplySpec {
                        resource_types: None,
                        principal_types: None,
                        context: AttributesOrContext(SchemaType::Type(SchemaTypeVariant::Record {
                            attributes: rec,
                            additional_attributes: false,
                        })),
                    }),
                (
                    choice((
                        accept(Token::VarPrincipal).map(|_| "principal"),
                        accept(Token::VarResource).map(|_| "resource"),
                    )),
                    accept(Token::Colon),
                    choice((parse_path().map(|p| vec![p]), parse_ets())),
                )
                    .map(|(id, _, ty)| match id {
                        "principal" => ApplySpec {
                            resource_types: None,
                            principal_types: Some(
                                ty.into_iter()
                                    .map(|n| SmolStr::new(n.to_string()))
                                    .collect_vec(),
                            ),
                            context: AttributesOrContext::default(),
                        },
                        "resource" => ApplySpec {
                            resource_types: Some(
                                ty.into_iter()
                                    .map(|n| SmolStr::new(n.to_string()))
                                    .collect_vec(),
                            ),
                            principal_types: None,
                            context: AttributesOrContext::default(),
                        },
                        _ => unreachable!("wrong id"),
                    }),
            )),
            optional(choice((
                (accept(Token::Comma), AppParser()).map(|(_, cdr)| cdr),
                accept(Token::Comma).map(|_| ApplySpec {
                    resource_types: None,
                    principal_types: None,
                    context: AttributesOrContext::default(),
                }),
            ))),
        )
            .map(|(singleton, cdr)| {
                if let Some(cdr) = cdr {
                    let merge = |lst1: Option<Vec<SmolStr>>, lst2| match (lst1, lst2) {
                        (Some(l1), Some(l2)) => Some([l1, l2].concat()),
                        (Some(l1), None) => Some(l1),
                        (None, Some(l2)) => Some(l2),
                        _ => None,
                    };
                    let lst = ApplySpec {
                        principal_types: merge(singleton.principal_types, cdr.principal_types),
                        resource_types: merge(singleton.resource_types, cdr.resource_types),
                        context: AttributesOrContext::default(),
                    };
                    lst
                } else {
                    singleton
                }
            })
            .parse(input)
    }
}

struct AttrParser();

impl<'a> Parser<TokenStream<'a>> for AttrParser {
    type Output = BTreeMap<SmolStr, TypeOfAttribute>;
    type PartialState = ();
    fn parse_lazy(
        &mut self,
        input: &mut TokenStream<'a>,
    ) -> combine::ParseResult<Self::Output, <TokenStream<'a> as combine::StreamOnce>::Error> {
        match self.parse(input.clone()) {
            Ok((res, tokens)) => {
                *input = tokens;
                combine::ParseResult::CommitOk(res)
            }
            Err(err) => combine::ParseResult::PeekErr(combine::error::Tracked::from(err)),
        }
    }
    // AttrDecls := Name ['?'] ':' Type [',' | ',' AttrDecls]
    fn parse(
        &mut self,
        input: TokenStream<'a>,
    ) -> Result<(Self::Output, TokenStream<'a>), <TokenStream<'a> as combine::StreamOnce>::Error>
    {
        (
            parse_name(),
            optional(accept(Token::Question)),
            accept(Token::Colon),
            parse_type(),
            optional(choice((
                (accept(Token::Comma), AttrParser()).map(|(_, attrs)| attrs),
                accept(Token::Comma).map(|_| BTreeMap::new()),
            ))),
        )
            .map(|(id, q, _, ty, rs)| {
                let mut pairs = BTreeMap::new();
                pairs.insert(
                    SmolStr::new(id.as_ref()),
                    TypeOfAttribute {
                        ty,
                        required: q.is_none(),
                    },
                );
                if let Some(rs) = rs {
                    pairs.extend(rs);
                }
                pairs
            })
            .parse(input)
    }
}

struct TypeParser();

impl<'a> Parser<TokenStream<'a>> for TypeParser {
    type Output = SchemaType;
    type PartialState = ();

    fn parse_lazy(
        &mut self,
        input: &mut TokenStream<'a>,
    ) -> combine::ParseResult<Self::Output, <TokenStream<'a> as combine::StreamOnce>::Error> {
        match self.parse(input.clone()) {
            Ok((res, tokens)) => {
                *input = tokens;
                combine::ParseResult::CommitOk(res)
            }
            Err(err) => combine::ParseResult::PeekErr(combine::error::Tracked::from(err)),
        }
    }

    fn parse(
        &mut self,
        input: TokenStream<'a>,
    ) -> Result<(Self::Output, TokenStream<'a>), <TokenStream<'a> as combine::StreamOnce>::Error>
    {
        choice((
            accept(Token::TyBool).map(|_| SchemaType::Type(SchemaTypeVariant::Boolean)),
            accept(Token::TyLong).map(|_| SchemaType::Type(SchemaTypeVariant::Long)),
            accept(Token::TyString).map(|_| SchemaType::Type(SchemaTypeVariant::String)),
            (
                accept(Token::Set),
                between(accept(Token::LAngle), accept(Token::RAngle), parse_type()),
            )
                .map(|(_, elem_ty)| {
                    SchemaType::Type(SchemaTypeVariant::Set {
                        element: (Box::new(elem_ty)),
                    })
                }),
            parse_rec_type().map(|attrs| {
                SchemaType::Type(SchemaTypeVariant::Record {
                    attributes: attrs,
                    additional_attributes: false,
                })
            }),
            parse_id().map(|id| {
                SchemaType::Type(SchemaTypeVariant::Entity {
                    name: SmolStr::new(id.as_ref()),
                })
            }),
        ))
        .parse(input)
    }
}

fn parse_type<'a>() -> impl Parser<TokenStream<'a>, Output = SchemaType> {
    TypeParser()
}

fn parse_decls<'a>() -> impl Parser<TokenStream<'a>, Output = NamespaceDefinition> {
    let merge_nds = |nds: Vec<NamespaceDefinition>| {
        let mut common_types = HashMap::new();
        let mut entity_types = HashMap::new();
        let mut actions = HashMap::new();
        for nd in nds.into_iter() {
            common_types.extend(nd.common_types);
            entity_types.extend(nd.entity_types);
            actions.extend(nd.actions);
        }
        NamespaceDefinition {
            common_types,
            entity_types,
            actions,
        }
    };
    // cannot be `many` otherwise there will be an infinite recursion
    many1(choice((
        parse_et_decl().map(|et| NamespaceDefinition {
            common_types: HashMap::new(),
            entity_types: HashMap::from_iter(et.into_iter()),
            actions: HashMap::new(),
        }),
        parse_action_decl().map(|action| NamespaceDefinition {
            common_types: HashMap::new(),
            entity_types: HashMap::new(),
            actions: action,
        }),
        parse_common_type_decl().map(|ct| NamespaceDefinition {
            common_types: HashMap::from_iter(std::iter::once(ct)),
            entity_types: HashMap::new(),
            actions: HashMap::new(),
        }),
    )))
    .map(move |nds: Vec<NamespaceDefinition>| merge_nds(nds))
}

fn parse_name<'a>() -> impl Parser<TokenStream<'a>, Output = SmolStr> {
    satisfy_map(|v| match v {
        (Token::Str(s), _) => Some(s),
        (Token::Identifier(id), _) => Some(id),
        _ => None,
    })
}

fn parse_names<'a>() -> impl Parser<TokenStream<'a>, Output = Vec<SmolStr>> {
    between(
        accept(Token::LBracket),
        accept(Token::RBracket),
        sep_by1(parse_name(), accept(Token::Comma)),
    )
}

fn parse_namespace<'a>() -> impl Parser<TokenStream<'a>, Output = (SmolStr, NamespaceDefinition)> {
    choice((
        (
            accept(Token::Namespace),
            parse_path(),
            between(accept(Token::LBrace), accept(Token::RBrace), parse_decls()),
        )
            .map(|(_, ns_str, ns_def)| (SmolStr::new(ns_str.to_string()), ns_def)),
        parse_decls().map(|ns_def| (SmolStr::new(""), ns_def)),
    ))
}

fn parse_path<'a>() -> impl Parser<TokenStream<'a>, Output = Name> {
    sep_by1(parse_id(), accept(Token::DoubleColon))
        .map(|ids: Vec<Id>| Name::new(ids[0].clone(), ids[1..].iter().map(|id| id.clone())))
}

// ActAttrs  := 'attributes' '{' AttrDecls '}'
// AppliesTo := 'appliesTo' '{' AppDecls '}'
// 'action' Names ['in' (Name | '[' [Names] ']')] [AppliesTo] [ActAttrs]';'
fn parse_action_decl<'a>() -> impl Parser<TokenStream<'a>, Output = HashMap<SmolStr, ActionType>> {
    (
        accept(Token::VarAction),
        sep_by1(parse_name(), accept(Token::Comma)).map(|vs: Vec<SmolStr>| vs),
        optional(
            (
                accept(Token::In),
                choice((parse_name().map(|p| vec![p]), parse_names())),
            )
                .map(|(_, ns)| ns),
        ),
        optional(
            (
                accept(Token::AppliesTo),
                between(accept(Token::LBrace), accept(Token::RBrace), AppParser()),
            )
                .map(|(_, apps)| apps),
        ),
        accept(Token::SemiColon),
    )
        .map(|(_, ids, ancestors, apps, _)| {
            HashMap::from_iter(ids.into_iter().map(|id| {
                (
                    SmolStr::new(id),
                    ActionType {
                        attributes: None,
                        applies_to: apps.clone(),
                        member_of: ancestors.clone().map(|ns| {
                            ns.into_iter()
                                .map(|n| ActionEntityUID { id: n, ty: None })
                                .collect_vec()
                        }),
                    },
                )
            }))
        })
}

// RecType   := '{' [AttrDecls] '}'
fn parse_rec_type<'a>() -> impl Parser<TokenStream<'a>, Output = BTreeMap<SmolStr, TypeOfAttribute>>
{
    between(
        accept(Token::LBrace),
        accept(Token::RBrace),
        optional(AttrParser()),
    )
    .map(|o| o.unwrap_or(BTreeMap::new()))
}

// Entity    := 'entity' Idents ['in' EntOrTyps] [['='] RecType] ';'
fn parse_et_decl<'a>() -> impl Parser<TokenStream<'a>, Output = Vec<(SmolStr, EntityType)>> {
    (
        accept(Token::Entity),
        parse_ids(),
        optional((
            accept(Token::In),
            choice((parse_path().map(|p| vec![p]), parse_ets())),
        ))
        .map(|opt| {
            if let Some((_, vs)) = opt {
                vs
            } else {
                Vec::new()
            }
        }),
        optional((optional(accept(Token::Eq)), parse_rec_type()).map(|(_, attrs)| attrs)).map(
            |opt| {
                if let Some(attrs) = opt {
                    AttributesOrContext(SchemaType::Type(SchemaTypeVariant::Record {
                        attributes: attrs,
                        additional_attributes: false,
                    }))
                } else {
                    AttributesOrContext::default()
                }
            },
        ),
        accept(Token::SemiColon),
    )
        .map(|(_, ids, ancestors, attrs, _)| {
            ids.iter()
                .map(|id| {
                    (
                        SmolStr::new(id),
                        EntityType {
                            member_of_types: ancestors
                                .clone()
                                .into_iter()
                                .map(|n| SmolStr::new(n.to_string()))
                                .collect_vec(),
                            shape: attrs.clone(),
                        },
                    )
                })
                .collect()
        })
}

// '[' [EntTypes] ']'
fn parse_ets<'a>() -> impl Parser<TokenStream<'a>, Output = Vec<Name>> {
    between(
        accept(Token::LBracket),
        accept(Token::RBracket),
        optional(sep_by1(parse_path(), accept(Token::Comma))).map(|o| o.unwrap_or(Vec::new())),
    )
}

// TypeDecl  := 'type' IDENT '=' Type ';'
fn parse_common_type_decl<'a>() -> impl Parser<TokenStream<'a>, Output = (SmolStr, SchemaType)> {
    (
        accept(Token::Type),
        parse_id().map(|id| SmolStr::new(id.as_ref())),
        accept(Token::Eq),
        parse_type(),
        accept(Token::SemiColon),
    )
        .map(|(_, id, _, ty, _)| (id, ty))
}

fn get_tokens(input: &str) -> Result<Vec<(Token, Span)>, ParseErrors> {
    Token::lexer(input)
        .spanned()
        .map(|(token, span)| match token {
            Ok(t) => Ok((t, span)),
            Err(_) => Err(ParseErrors::Lexing(SmolStr::new(format!("{span:?}")))),
        })
        .collect()
}

fn parse_namespaces<'a>(
) -> impl Parser<TokenStream<'a>, Output = Vec<(SmolStr, NamespaceDefinition)>> {
    (many(parse_namespace()), eof::<TokenStream<'a>>()).0
}

pub fn parse_schema_fragment_from_str(input: &str) -> Result<SchemaFragment, ParseErrors> {
    let tokens = get_tokens(input)?;
    let (namespaces, _) = parse_namespaces().parse(TokenStream {
        token_spans: &tokens,
    })?;
    let mut map = HashMap::new();
    for (id, ns) in namespaces {
        if map.contains_key(&id) {
            return Err(ParseErrors::Other(SmolStr::new(format!(
                "duplicate namespace id: {}",
                id
            ))));
        }
        map.insert(id, ns);
    }
    Ok(SchemaFragment(map))
}

#[cfg(test)]
mod test_parser {
    use super::*;
    use combine::Parser;
    #[test]
    fn test_parse_id() {
        let tokens = get_tokens(",lollol").expect("lexing is ok");
        let id = parse_path().parse(TokenStream {
            token_spans: &tokens,
        });
        assert!(id.is_err(), "{:?}", id.unwrap());
    }
    #[test]
    fn test_parse_type() {
        let tokens = get_tokens("{lol: Set <String>, abc: { efg: Bool}}").expect("lexing is ok");
        let ty = parse_type()
            .parse(TokenStream {
                token_spans: &tokens,
            })
            .expect("should parse")
            .0;
        assert!(
            ty != SchemaType::Type(SchemaTypeVariant::Set {
                element: Box::new(SchemaType::Type(SchemaTypeVariant::String))
            }),
            "{ty:?}"
        );
    }
    #[test]
    fn test_parse_et_decl() {
        let tokens = get_tokens(" entity User in [Team,Application] { name: String };")
            .expect("lexing is ok");
        let et = parse_et_decl().parse(TokenStream {
            token_spans: &tokens,
        });
        assert!(et.is_ok());
    }
    #[test]
    fn test_parse_action_decl() {
        let tokens = get_tokens(
            " action CreateList
            appliesTo { principal: [User], resource: [Application] };",
        )
        .expect("lexing is ok");
        let action = parse_action_decl().parse(TokenStream {
            token_spans: &tokens,
        });
        assert!(action.is_ok(), "{:?}", action.unwrap_err());
    }
    #[test]
    fn test_parse_common_type_decl() {
        let tokens = get_tokens(
            "type authcontext = {
                ip: ipaddr,
                is_authenticated: Boolean,
                timestamp: Long
            };",
        )
        .expect("lexing is ok");
        let ty = parse_common_type_decl().parse(TokenStream {
            token_spans: &tokens,
        });
        assert!(ty.is_ok());
    }
    #[test]
    fn test_parse_ns_decl() {
        let tokens = get_tokens(
            r#"namespace go {
                entity Application;
                entity User in [Team,Application] { name: String };
                entity Team in [Team,Application];
                entity List in [Application] {
                    owner: User,
                    name: String,
                    readers: Team,
                    editors: Team,
                    tasks: Set<{name: String, id: Long, state: String}>
                };

                action CreateList, GetLists
                    appliesTo { principal: [User], resource: [Application] };

                action GetList, UpdateList, DeleteList, CreateTask, UpdateTask, DeleteTask, EditShares
                    appliesTo { principal: [User], resource:[List] };
            }"#,
        ).expect("lexing is ok");
        let ns = parse_namespace().parse(TokenStream {
            token_spans: &tokens,
        });
        assert!(ns.is_ok(), "{:?}", ns.unwrap_err());
    }
}

#[cfg(test)]
mod test_lexer {
    use super::Token;
    use logos::Logos;
    #[test]
    fn example() {
        let tokens: Vec<_> = Token::lexer(
            r#"namespace "" {
            entity Application;
            entity User in [Team,Application] { name: String };
            entity Team in [Team,Application];
            entity List in [Application] {
                owner: User,
                name: String,
                readers: Team,
                editors: Team,
                tasks: Set<{name: String, id: Long, state: String}>
            };

            action CreateList, GetLists
                appliesTo { principal: [User], resource: [Application] };

            action GetList, UpdateList, DeleteList, CreateTask, UpdateTask, DeleteTask, EditShares
                appliesTo { principal: [User], resource:[List] };
        }"#,
        )
        .spanned()
        .collect();
        assert!(tokens.into_iter().all(|(t, _)| t.is_ok()));
    }
}
