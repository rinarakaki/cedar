//! Tests described in https://github.com/cedar-policy/cedar/issues/579
//!
//! We test all possible (position, scenario) pairs where:
//!
//! position is all places a typename can occur in a schema:
//! A. Inside a context attribute type
//! B. Inside an entity attribute type
//! C. Inside the body of a common-type definition
//! D. As an entity parent type
//! E. In an action `appliesTo` declaration
//! F. Inside an action attribute type?
//! G. In an action parent declaration?
//!
//! and scenario is all the ways a typename can resolve:
//! 1. the typename is written without a namespace
//!     a. and that typename is declared in the current namespace (but not the empty namespace)
//!         1. as an entity type
//!         2. as a common type
//!     b. and that typename is declared in the empty namespace (but not the current namespace)
//!         1. as an entity type
//!         2. as a common type
//!     c. and that typename is not declared in either the current namespace or the empty namespace
//! 2. the typename is written _with_ the current namespace explicit
//!     a. and that typename is declared in the current namespace (but not the empty namespace)
//!         1. as an entity type
//!         2. as a common type
//!     b. and that typename is declared in the empty namespace (but not the current namespace)
//!         1. as an entity type
//!         2. as a common type
//!     c. and that typename is not declared in either the current namespace or the empty namespace
//! 3. the typename is written _with_ an explicit namespace NS (not the current namespace)
//!     a. and that typename is declared in the current namespace (but not the empty namespace or NS)
//!         1. as an entity type
//!         2. as a common type
//!     b. and that typename is declared in the empty namespace (but not the current namespace or NS)
//!         1. as an entity type
//!         2. as a common type
//!     c. and that typename is not declared in the current namespace, the empty namespace, or NS
//!     d. and that typename is declared in NS (and also the current namespace, but not the empty namespace)
//!         1. as an entity type
//!         2. as a common type
//!
//! We also repeat all of these tests with both the human syntax and the JSON syntax.
//! The JSON syntax distinguishes syntactically between entity and common type _references_;
//! we only do the test for the more sensible one. (For instance, for 1a1, we
//! only test an entity type reference, not a common type reference.)

use super::{SchemaWarning, ValidatorSchema};
use cedar_policy_core::extensions::Extensions;
use cedar_policy_core::test_utils::{
    expect_err, ExpectedErrorMessage, ExpectedErrorMessageBuilder,
};
use cool_asserts::assert_matches;
use serde_json::json;

/// Transform the output of functions like
/// `ValidatorSchema::from_str_natural()`, which has type `(ValidatorSchema, impl Iterator<...>)`,
/// into `(ValidatorSchema, Vec<...>)`, which implements `Debug` and thus can be used with
/// `assert_matches`, `.unwrap_err()`, etc
fn collect_warnings<A, B, E>(r: Result<(A, impl Iterator<Item = B>), E>) -> Result<(A, Vec<B>), E> {
    r.map(|(a, iter)| (a, iter.collect()))
}

#[track_caller]
fn assert_parses_successfully_human(s: &str) -> (ValidatorSchema, Vec<SchemaWarning>) {
    println!("{s}");
    collect_warnings(ValidatorSchema::from_str_natural(
        s,
        Extensions::all_available(),
    ))
    .map_err(miette::Report::new)
    .unwrap()
}

#[track_caller]
fn assert_parses_successfully_json(v: serde_json::Value) -> ValidatorSchema {
    println!("{}", serde_json::to_string_pretty(&v).unwrap());
    ValidatorSchema::from_json_value(v, Extensions::all_available())
        .map_err(miette::Report::new)
        .unwrap()
}

#[track_caller]
fn assert_parse_error_human(s: &str, e: &ExpectedErrorMessage<'_>) {
    println!("{s}");
    assert_matches!(collect_warnings(ValidatorSchema::from_str_natural(s, Extensions::all_available())), Err(err) => {
        expect_err(s, &miette::Report::new(err), e);
    });
}

#[track_caller]
fn assert_parse_error_json(v: serde_json::Value, e: &ExpectedErrorMessage<'_>) {
    println!("{}", serde_json::to_string_pretty(&v).unwrap());
    assert_matches!(ValidatorSchema::from_json_value(v.clone(), Extensions::all_available()), Err(err) => {
        expect_err(&v, &miette::Report::new(err), e);
    });
}

/// Makes a schema for all the XXa1 test cases, where different XX plug in
/// different `mytype_use` (schema constructs that use `MyType`).
///
/// In all of these cases, `MyType` is declared as an entity type in the
/// current namespace (NS1).
fn a1_human(mytype_use: &str) -> String {
    format!(
        r#"
        namespace NS1 {{
            entity User, Resource;
            entity MyType;
            {mytype_use}
        }}
        "#
    )
}

/// Makes a schema for all the XXa1 test cases, where different XX plug in a
/// different schema construct that uses `MyType` (e.g., with a function
/// like `A1X1_json()`).
///
/// In all of these cases, `MyType` is declared as an entity type in the
/// current namespace (NS1).
fn a1_json() -> serde_json::Value {
    json!({
        "NS1": {
            "entityTypes": {
                "User": { "memberOfTypes": [] },
                "Resource": { "memberOfTypes": [] },
                "MyType": { "memberOfTypes": [] },
            },
            "actions": {}
        }
    })
}

/// Makes a schema for all the XXa2 test cases, where different XX plug in
/// different `mytype_use` (schema constructs that use `MyType`).
///
/// In all of these cases, `MyType` is declared as a common type in the
/// current namespace (NS1).
fn a2_human(mytype_use: &str) -> String {
    format!(
        r#"
        namespace NS1 {{
            entity User, Resource;
            type MyType = String;
            {mytype_use}
        }}
        "#
    )
}

/// Makes a schema for all the XXa2 test cases, where different XX plug in a
/// different schema construct that uses `MyType` (e.g., with a function
/// like `A1X1_json()`).
///
/// In all of these cases, `MyType` is declared as a common type in the
/// current namespace (NS1).
fn a2_json() -> serde_json::Value {
    json!({
        "NS1": {
            "entityTypes": {
                "User": { "memberOfTypes": [] },
                "Resource": { "memberOfTypes": [] },
            },
            "commonTypes": {
                "MyType": { "type": "String" },
            },
            "actions": {}
        }
    })
}

/// Makes a schema for all the XXb1 test cases, where different XX plug in
/// different `mytype_use` (schema constructs that use `MyType`).
///
/// In all of these cases, `MyType` is declared as an entity type in the
/// empty namespace.
fn b1_human(mytype_use: &str) -> String {
    format!(
        r#"
        entity MyType;
        namespace NS1 {{
            entity User, Resource;
            {mytype_use}
        }}
        "#
    )
}

/// Makes a schema for all the XXb1 test cases, where different XX plug in a
/// different schema construct that uses `MyType` (e.g., with a function
/// like `A1X1_json()`).
///
/// In all of these cases, `MyType` is declared as an entity type in the
/// empty namespace.
fn b1_json() -> serde_json::Value {
    json!({
        "": {
            "entityTypes": {
                "MyType": { "memberOfTypes": [] }
            },
            "actions": {}
        },
        "NS1": {
            "entityTypes": {
                "User": { "memberOfTypes": [] },
                "Resource": { "memberOfTypes": [] },
            },
            "actions": {}
        }
    })
}

/// Makes a schema for all the XXb2 test cases, where different XX plug in
/// different `mytype_use` (schema constructs that use `MyType`).
///
/// In all of these cases, `MyType` is declared as a common type in the
/// empty namespace.
fn b2_human(mytype_use: &str) -> String {
    format!(
        r#"
        type MyType = String;
        namespace NS1 {{
            entity User, Resource;
            {mytype_use}
        }}
        "#
    )
}

/// Makes a schema for all the XXb2 test cases, where different XX plug in a
/// different schema construct that uses `MyType` (e.g., with a function
/// like `A1X1_json()`).
///
/// In all of these cases, `MyType` is declared as a common type in the
/// empty namespace.
fn b2_json() -> serde_json::Value {
    json!({
        "": {
            "commonTypes": {
                "MyType": { "type": "String" }
            },
            "entityTypes": {},
            "actions": {}
        },
        "NS1": {
            "entityTypes": {
                "User": { "memberOfTypes": [] },
                "Resource": { "memberOfTypes": [] },
            },
            "actions": {}
        }
    })
}

/// Makes a schema for all the XXc test cases, where different XX plug in
/// different `mytype_use` (schema constructs that use `MyType`).
///
/// In all of these cases, `MyType` is not declared in any namespace.
fn c_human(mytype_use: &str) -> String {
    format!(
        r#"
        namespace NS1 {{
            entity User, Resource;
            {mytype_use}
        }}
        "#
    )
}

/// Makes a schema for all the XXc test cases, where different XX plug in a
/// different schema construct that uses `MyType` (e.g., with a function
/// like `A1X1_json()`).
///
/// In all of these cases, `MyType` is not declared in any namespace.
fn c_json() -> serde_json::Value {
    json!({
        "NS1": {
            "entityTypes": {
                "User": { "memberOfTypes": [] },
                "Resource": { "memberOfTypes": [] },
            },
            "actions": {}
        }
    })
}

/// Makes a schema for all the XXd1 test cases, where different XX plug in
/// different `mytype_use` (schema constructs that use `MyType`).
///
/// In all of these cases, `MyType` is declared as an entity type in an
/// unrelated namespace (NS2).
fn d1_human(mytype_use: &str) -> String {
    format!(
        r#"
        namespace NS2 {{
            entity MyType;
        }}
        namespace NS1 {{
            entity User, Resource;
            {mytype_use}
        }}
        "#
    )
}

/// Makes a schema for all the XXd1 test cases, where different XX plug in a
/// different schema construct that uses `MyType` (e.g., with a function
/// like `A1X1_json()`).
///
/// In all of these cases, `MyType` is declared as an entity type in an
/// unrelated namespace (NS2).
fn d1_json() -> serde_json::Value {
    json!({
        "NS2": {
            "entityTypes": {
                "MyType": { "memberOfTypes": [] },
            },
            "actions": {}
        },
        "NS1": {
            "entityTypes": {
                "User": { "memberOfTypes": [] },
                "Resource": { "memberOfTypes": [] },
            },
            "actions": {}
        }
    })
}

/// Makes a schema for all the XXd2 test cases, where different XX plug in
/// different `mytype_use` (schema constructs that use `MyType`).
///
/// In all of these cases, `MyType` is declared as a common type in an
/// unrelated namespace (NS2).
fn d2_human(mytype_use: &str) -> String {
    format!(
        r#"
        namespace NS2 {{
            type MyType = String;
        }}
        namespace NS1 {{
            entity User, Resource;
            {mytype_use}
        }}
        "#
    )
}

/// Makes a schema for all the XXd2 test cases, where different XX plug in a
/// different schema construct that uses `MyType` (e.g., with a function
/// like `A1X1_json()`).
///
/// In all of these cases, `MyType` is declared as a common type in an
/// unrelated namespace (NS2).
fn d2_json() -> serde_json::Value {
    json!({
        "NS2": {
            "commonTypes": {
                "MyType": { "type": "String" },
            },
            "entityTypes": {},
            "actions": {}
        },
        "NS1": {
            "entityTypes": {
                "User": { "memberOfTypes": [] },
                "Resource": { "memberOfTypes": [] },
            },
            "actions": {}
        }
    })
}

/// Generate human-schema syntax for a `MyType` use of kind A1.
fn A1_human() -> &'static str {
    r#"action Read appliesTo { principal: [User], resource: [Resource], context: { foo: MyType }};"#
}

/// Given a starting JSON schema (e.g., from `a1_json()`),
/// add a `MyType` use of kind A1X1 (for any X), returning the new schema.
fn A1X1_json(mut schema: serde_json::Value) -> serde_json::Value {
    schema["NS1"]["actions"]["Read"] = json!({
        "appliesTo": {
            "principalTypes": ["User"],
            "resourceTypes": ["Resource"],
            "context": {
                "type": "Record",
                "attributes": {
                    "foo": { "type": "Entity", "name": "MyType" }
                }
            }
        }
    });
    schema
}

/// Given a starting JSON schema (e.g., from `a1_json()`),
/// add a `MyType` use of kind A1X2 (for any X), returning the new schema.
fn A1X2_json(mut schema: serde_json::Value) -> serde_json::Value {
    schema["NS1"]["actions"]["Read"] = json!({
        "appliesTo": {
            "principalTypes": ["User"],
            "resourceTypes": ["Resource"],
            "context": {
                "type": "Record",
                "attributes": {
                    "foo": { "type": "MyType" }
                }
            }
        }
    });
    schema
}

/// Generate human-schema syntax for a `MyType` use of kind A2.
fn A2_human() -> &'static str {
    r#"action Read appliesTo { principal: [User], resource: [Resource], context: { foo: NS1::MyType }};"#
}

/// Given a starting JSON schema (e.g., from `a1_json()`),
/// add a `MyType` use of kind A2X1 (for any X), returning the new schema.
fn A2X1_json(mut schema: serde_json::Value) -> serde_json::Value {
    schema["NS1"]["actions"]["Read"] = json!({
        "appliesTo": {
            "principalTypes": ["User"],
            "resourceTypes": ["Resource"],
            "context": {
                "type": "Record",
                "attributes": {
                    "foo": { "type": "Entity", "name": "NS1::MyType" }
                }
            }
        }
    });
    schema
}

/// Given a starting JSON schema (e.g., from `a1_json()`),
/// add a `MyType` use of kind A2X2 (for any X), returning the new schema.
fn A2X2_json(mut schema: serde_json::Value) -> serde_json::Value {
    schema["NS1"]["actions"]["Read"] = json!({
        "appliesTo": {
            "principalTypes": ["User"],
            "resourceTypes": ["Resource"],
            "context": {
                "type": "Record",
                "attributes": {
                    "foo": { "type": "NS1::MyType" }
                }
            }
        }
    });
    schema
}

/// Generate human-schema syntax for a `MyType` use of kind A3.
fn A3_human() -> &'static str {
    r#"action Read appliesTo { principal: [User], resource: [Resource], context: { foo: NS2::MyType }};"#
}

/// Given a starting JSON schema (e.g., from `a1_json()`),
/// add a `MyType` use of kind A3X1 (for any X), returning the new schema.
fn A3X1_json(mut schema: serde_json::Value) -> serde_json::Value {
    schema["NS1"]["actions"]["Read"] = json!({
        "appliesTo": {
            "principalTypes": ["User"],
            "resourceTypes": ["Resource"],
            "context": {
                "type": "Record",
                "attributes": {
                    "foo": { "type": "Entity", "name": "NS2::MyType" }
                }
            }
        }
    });
    schema
}

/// Given a starting JSON schema (e.g., from `a1_json()`),
/// add a `MyType` use of kind A3X2 (for any X), returning the new schema.
fn A3X2_json(mut schema: serde_json::Value) -> serde_json::Value {
    schema["NS1"]["actions"]["Read"] = json!({
        "appliesTo": {
            "principalTypes": ["User"],
            "resourceTypes": ["Resource"],
            "context": {
                "type": "Record",
                "attributes": {
                    "foo": { "type": "NS2::MyType" }
                }
            }
        }
    });
    schema
}

/// Generate human-schema syntax for a `MyType` use of kind B1.
fn B1_human() -> &'static str {
    r#"entity E { foo: MyType };"#
}

/// Given a starting JSON schema (e.g., from `a1_json()`),
/// add a `MyType` use of kind B1X1 (for any X), returning the new schema.
fn B1X1_json(mut schema: serde_json::Value) -> serde_json::Value {
    schema["NS1"]["entityTypes"]["E"] = json!({
        "memberOfTypes": [],
        "shape": {
            "type": "Record",
            "attributes": {
                "foo": { "type": "Entity", "name": "MyType" }
            }
        }
    });
    schema
}

/// Given a starting JSON schema (e.g., from `a1_json()`),
/// add a `MyType` use of kind B1X2 (for any X), returning the new schema.
fn B1X2_json(mut schema: serde_json::Value) -> serde_json::Value {
    schema["NS1"]["entityTypes"]["E"] = json!({
        "memberOfTypes": [],
        "shape": {
            "type": "Record",
            "attributes": {
                "foo": { "type": "MyType" }
            }
        }
    });
    schema
}

/// Generate human-schema syntax for a `MyType` use of kind B2.
fn B2_human() -> &'static str {
    r#"entity E { foo: NS1::MyType };"#
}

/// Given a starting JSON schema (e.g., from `a1_json()`),
/// add a `MyType` use of kind B2X1 (for any X), returning the new schema.
fn B2X1_json(mut schema: serde_json::Value) -> serde_json::Value {
    schema["NS1"]["entityTypes"]["E"] = json!({
        "memberOfTypes": [],
        "shape": {
            "type": "Record",
            "attributes": {
                "foo": { "type": "Entity", "name": "NS1::MyType" }
            }
        }
    });
    schema
}

/// Given a starting JSON schema (e.g., from `a1_json()`),
/// add a `MyType` use of kind B2X2 (for any X), returning the new schema.
fn B2X2_json(mut schema: serde_json::Value) -> serde_json::Value {
    schema["NS1"]["entityTypes"]["E"] = json!({
        "memberOfTypes": [],
        "shape": {
            "type": "Record",
            "attributes": {
                "foo": { "type": "NS1::MyType" }
            }
        }
    });
    schema
}

/// Generate human-schema syntax for a `MyType` use of kind B3.
fn B3_human() -> &'static str {
    r#"entity E { foo: NS2::MyType };"#
}

/// Given a starting JSON schema (e.g., from `a1_json()`),
/// add a `MyType` use of kind B3X1 (for any X), returning the new schema.
fn B3X1_json(mut schema: serde_json::Value) -> serde_json::Value {
    schema["NS1"]["entityTypes"]["E"] = json!({
        "memberOfTypes": [],
        "shape": {
            "type": "Record",
            "attributes": {
                "foo": { "type": "Entity", "name": "NS2::MyType" }
            }
        }
    });
    schema
}

/// Given a starting JSON schema (e.g., from `a1_json()`),
/// add a `MyType` use of kind B3X2 (for any X), returning the new schema.
fn B3X2_json(mut schema: serde_json::Value) -> serde_json::Value {
    schema["NS1"]["entityTypes"]["E"] = json!({
        "memberOfTypes": [],
        "shape": {
            "type": "Record",
            "attributes": {
                "foo": { "type": "NS2::MyType" }
            }
        }
    });
    schema
}

/// Generate human-schema syntax for a `MyType` use of kind C1.
fn C1_human() -> &'static str {
    r#"type E = { foo: MyType };"#
}

/// Given a starting JSON schema (e.g., from `a1_json()`),
/// add a `MyType` use of kind C1X1 (for any X), returning the new schema.
fn C1X1_json(mut schema: serde_json::Value) -> serde_json::Value {
    schema["NS1"]["commonTypes"]["E"] = json!({
        "type": "Record",
        "attributes": {
            "foo": { "type": "Entity", "name": "MyType" }
            }
    });
    schema
}

/// Given a starting JSON schema (e.g., from `a1_json()`),
/// add a `MyType` use of kind C1X2 (for any X), returning the new schema.
fn C1X2_json(mut schema: serde_json::Value) -> serde_json::Value {
    schema["NS1"]["commonTypes"]["E"] = json!({
        "type": "Record",
        "attributes": {
            "foo": { "type": "MyType" }
        }
    });
    schema
}

/// Generate human-schema syntax for a `MyType` use of kind C2.
fn C2_human() -> &'static str {
    r#"type E = { foo: NS1::MyType };"#
}

/// Given a starting JSON schema (e.g., from `a1_json()`),
/// add a `MyType` use of kind C2X1 (for any X), returning the new schema.
fn C2X1_json(mut schema: serde_json::Value) -> serde_json::Value {
    schema["NS1"]["commonTypes"]["E"] = json!({
        "type": "Record",
        "attributes": {
            "foo": { "type": "Entity", "name": "NS1::MyType" }
            }
    });
    schema
}

/// Given a starting JSON schema (e.g., from `a1_json()`),
/// add a `MyType` use of kind C2X2 (for any X), returning the new schema.
fn C2X2_json(mut schema: serde_json::Value) -> serde_json::Value {
    schema["NS1"]["commonTypes"]["E"] = json!({
        "type": "Record",
        "attributes": {
            "foo": { "type": "NS1::MyType" }
        }
    });
    schema
}

/// Generate human-schema syntax for a `MyType` use of kind C3.
fn C3_human() -> &'static str {
    r#"type E = { foo: NS2::MyType };"#
}

/// Given a starting JSON schema (e.g., from `a1_json()`),
/// add a `MyType` use of kind C3X1 (for any X), returning the new schema.
fn C3X1_json(mut schema: serde_json::Value) -> serde_json::Value {
    schema["NS1"]["commonTypes"]["E"] = json!({
        "type": "Record",
        "attributes": {
            "foo": { "type": "Entity", "name": "NS2::MyType" }
            }
    });
    schema
}

/// Given a starting JSON schema (e.g., from `a1_json()`),
/// add a `MyType` use of kind C3X2 (for any X), returning the new schema.
fn C3X2_json(mut schema: serde_json::Value) -> serde_json::Value {
    schema["NS1"]["commonTypes"]["E"] = json!({
        "type": "Record",
        "attributes": {
            "foo": { "type": "NS2::MyType" }
        }
    });
    schema
}

// ####
//
// For explanations of all of the below tests and their naming, see comments
// on this module.
//
// ####

// human versions
#[test]
fn A1a1_human() {
    assert_parses_successfully_human(&a1_human(A1_human()));
}
#[test]
fn A1a2_human() {
    assert_parses_successfully_human(&a2_human(A1_human()));
}
#[test]
fn A1b1_human() {
    assert_parses_successfully_human(&b1_human(A1_human()));
}
#[test]
fn A1b2_human() {
    assert_parses_successfully_human(&b2_human(A1_human()));
}
#[test]
fn A1c_human() {
    assert_parse_error_human(
        &c_human(A1_human()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: MyType")
            .help("neither `NS1::MyType` nor `MyType` refers to anything that has been declared")
            // TODO: why don't we have an underline here? (Uncommenting this produces test failure)
            //.exactly_one_underline("MyType")
            .build(),
    );
}
#[test]
fn A2a1_human() {
    assert_parses_successfully_human(&a1_human(A2_human()));
}
#[test]
fn A2a2_human() {
    assert_parses_successfully_human(&a2_human(A2_human()));
}
#[test]
fn A2b1_human() {
    assert_parse_error_human(
        &b1_human(A2_human()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS1::MyType")
            .help("`NS1::MyType` has not been declared")
            // TODO: why don't we have an underline here? (Uncommenting this produces test failure)
            //.exactly_one_underline("NS1::MyType")
            .build(),
    );
}
#[test]
fn A2b2_human() {
    assert_parse_error_human(
        &b2_human(A2_human()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS1::MyType")
            .help("`NS1::MyType` has not been declared")
            // TODO: why don't we have an underline here? (Uncommenting this produces test failure)
            //.exactly_one_underline("NS1::MyType")
            .build(),
    );
}
#[test]
fn A2c_human() {
    assert_parse_error_human(
        &c_human(A2_human()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS1::MyType")
            .help("`NS1::MyType` has not been declared")
            // TODO: why don't we have an underline here? (Uncommenting this produces test failure)
            //.exactly_one_underline("NS1::MyType")
            .build(),
    );
}
#[test]
fn A3a1_human() {
    assert_parse_error_human(
        &a1_human(A3_human()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            // TODO: why don't we have an underline here? (Uncommenting this produces test failure)
            //.exactly_one_underline("NS2::MyType")
            .build(),
    );
}
#[test]
fn A3a2_human() {
    assert_parse_error_human(
        &a2_human(A3_human()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            // TODO: why don't we have an underline here? (Uncommenting this produces test failure)
            //.exactly_one_underline("NS2::MyType")
            .build(),
    );
}
#[test]
fn A3b1_human() {
    assert_parse_error_human(
        &b1_human(A3_human()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            // TODO: why don't we have an underline here? (Uncommenting this produces test failure)
            //.exactly_one_underline("NS2::MyType")
            .build(),
    );
}
#[test]
fn A3b2_human() {
    assert_parse_error_human(
        &b2_human(A3_human()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            // TODO: why don't we have an underline here? (Uncommenting this produces test failure)
            //.exactly_one_underline("NS2::MyType")
            .build(),
    );
}
#[test]
fn A3c_human() {
    assert_parse_error_human(
        &c_human(A3_human()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            // TODO: why don't we have an underline here? (Uncommenting this produces test failure)
            //.exactly_one_underline("NS1::MyType")
            .build(),
    );
}
#[test]
fn A3d1_human() {
    assert_parses_successfully_human(&d1_human(A3_human()));
}
#[test]
fn A3d2_human() {
    assert_parses_successfully_human(&d2_human(A3_human()));
}
#[test]
fn B1a1_human() {
    assert_parses_successfully_human(&a1_human(B1_human()));
}
#[test]
fn B1a2_human() {
    assert_parses_successfully_human(&a2_human(B1_human()));
}
#[test]
fn B1b1_human() {
    assert_parses_successfully_human(&b1_human(B1_human()));
}
#[test]
fn B1b2_human() {
    assert_parses_successfully_human(&b2_human(B1_human()));
}
#[test]
fn B1c_human() {
    assert_parse_error_human(
        &c_human(B1_human()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: MyType")
            .help("neither `NS1::MyType` nor `MyType` refers to anything that has been declared")
            // TODO: why don't we have an underline here? (Uncommenting this produces test failure)
            //.exactly_one_underline("MyType")
            .build(),
    );
}
#[test]
fn B2a1_human() {
    assert_parses_successfully_human(&a1_human(B2_human()));
}
#[test]
fn B2a2_human() {
    assert_parses_successfully_human(&a2_human(B2_human()));
}
#[test]
fn B2b1_human() {
    assert_parse_error_human(
        &b1_human(B2_human()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS1::MyType")
            .help("`NS1::MyType` has not been declared")
            // TODO: why don't we have an underline here? (Uncommenting this produces test failure)
            //.exactly_one_underline("NS1::MyType")
            .build(),
    );
}
#[test]
fn B2b2_human() {
    assert_parse_error_human(
        &b2_human(B2_human()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS1::MyType")
            .help("`NS1::MyType` has not been declared")
            // TODO: why don't we have an underline here? (Uncommenting this produces test failure)
            //.exactly_one_underline("NS1::MyType")
            .build(),
    );
}
#[test]
fn B2c_human() {
    assert_parse_error_human(
        &c_human(B2_human()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS1::MyType")
            .help("`NS1::MyType` has not been declared")
            // TODO: why don't we have an underline here? (Uncommenting this produces test failure)
            //.exactly_one_underline("NS1::MyType")
            .build(),
    );
}
#[test]
fn B3a1_human() {
    assert_parse_error_human(
        &a1_human(B3_human()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            // TODO: why don't we have an underline here? (Uncommenting this produces test failure)
            //.exactly_one_underline("NS2::MyType")
            .build(),
    );
}
#[test]
fn B3a2_human() {
    assert_parse_error_human(
        &a2_human(B3_human()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            // TODO: why don't we have an underline here? (Uncommenting this produces test failure)
            //.exactly_one_underline("NS2::MyType")
            .build(),
    );
}
#[test]
fn B3b1_human() {
    assert_parse_error_human(
        &b1_human(B3_human()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            // TODO: why don't we have an underline here? (Uncommenting this produces test failure)
            //.exactly_one_underline("NS2::MyType")
            .build(),
    );
}
#[test]
fn B3b2_human() {
    assert_parse_error_human(
        &b2_human(B3_human()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            // TODO: why don't we have an underline here? (Uncommenting this produces test failure)
            //.exactly_one_underline("NS2::MyType")
            .build(),
    );
}
#[test]
fn B3c_human() {
    assert_parse_error_human(
        &c_human(B3_human()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            // TODO: why don't we have an underline here? (Uncommenting this produces test failure)
            //.exactly_one_underline("NS1::MyType")
            .build(),
    );
}
#[test]
fn B3d1_human() {
    assert_parses_successfully_human(&d1_human(B3_human()));
}
#[test]
fn B3d2_human() {
    assert_parses_successfully_human(&d2_human(B3_human()));
}
#[test]
fn C1a1_human() {
    assert_parses_successfully_human(&a1_human(C1_human()));
}
#[test]
fn C1a2_human() {
    assert_parses_successfully_human(&a2_human(C1_human()));
}
#[test]
fn C1b1_human() {
    assert_parses_successfully_human(&b1_human(C1_human()));
}
#[test]
fn C1b2_human() {
    assert_parses_successfully_human(&b2_human(C1_human()));
}
#[test]
fn C1c_human() {
    assert_parse_error_human(
        &c_human(C1_human()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: MyType")
            .help("neither `NS1::MyType` nor `MyType` refers to anything that has been declared")
            // TODO: why don't we have an underline here? (Uncommenting this produces test failure)
            //.exactly_one_underline("MyType")
            .build(),
    );
}
#[test]
fn C2a1_human() {
    assert_parses_successfully_human(&a1_human(C2_human()));
}
#[test]
fn C2a2_human() {
    assert_parses_successfully_human(&a2_human(C2_human()));
}
#[test]
fn C2b1_human() {
    assert_parse_error_human(
        &b1_human(C2_human()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS1::MyType")
            .help("`NS1::MyType` has not been declared")
            // TODO: why don't we have an underline here? (Uncommenting this produces test failure)
            //.exactly_one_underline("NS1::MyType")
            .build(),
    );
}
#[test]
fn C2b2_human() {
    assert_parse_error_human(
        &b2_human(C2_human()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS1::MyType")
            .help("`NS1::MyType` has not been declared")
            // TODO: why don't we have an underline here? (Uncommenting this produces test failure)
            //.exactly_one_underline("NS1::MyType")
            .build(),
    );
}
#[test]
fn C2c_human() {
    assert_parse_error_human(
        &c_human(C2_human()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS1::MyType")
            .help("`NS1::MyType` has not been declared")
            // TODO: why don't we have an underline here? (Uncommenting this produces test failure)
            //.exactly_one_underline("NS1::MyType")
            .build(),
    );
}
#[test]
fn C3a1_human() {
    assert_parse_error_human(
        &a1_human(C3_human()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            // TODO: why don't we have an underline here? (Uncommenting this produces test failure)
            //.exactly_one_underline("NS2::MyType")
            .build(),
    );
}
#[test]
fn C3a2_human() {
    assert_parse_error_human(
        &a2_human(C3_human()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            // TODO: why don't we have an underline here? (Uncommenting this produces test failure)
            //.exactly_one_underline("NS2::MyType")
            .build(),
    );
}
#[test]
fn C3b1_human() {
    assert_parse_error_human(
        &b1_human(C3_human()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            // TODO: why don't we have an underline here? (Uncommenting this produces test failure)
            //.exactly_one_underline("NS2::MyType")
            .build(),
    );
}
#[test]
fn C3b2_human() {
    assert_parse_error_human(
        &b2_human(C3_human()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            // TODO: why don't we have an underline here? (Uncommenting this produces test failure)
            //.exactly_one_underline("NS2::MyType")
            .build(),
    );
}
#[test]
fn C3c_human() {
    assert_parse_error_human(
        &c_human(C3_human()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            // TODO: why don't we have an underline here? (Uncommenting this produces test failure)
            //.exactly_one_underline("NS1::MyType")
            .build(),
    );
}
#[test]
fn C3d1_human() {
    assert_parses_successfully_human(&d1_human(C3_human()));
}
#[test]
fn C3d2_human() {
    assert_parses_successfully_human(&d2_human(C3_human()));
}

// json versions
#[test]
fn A1a1_json() {
    assert_parses_successfully_json(A1X1_json(a1_json()));
}
#[test]
fn A1a2_json() {
    assert_parses_successfully_json(A1X2_json(a2_json()));
}
#[test]
fn A1b1_json() {
    assert_parses_successfully_json(A1X1_json(b1_json()));
}
#[test]
fn A1b2_json() {
    assert_parses_successfully_json(A1X2_json(b2_json()));
}
#[test]
fn A1c_json() {
    assert_parse_error_json(
        A1X1_json(c_json()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: MyType")
            .help("neither `NS1::MyType` nor `MyType` refers to anything that has been declared")
            .build(),
    );
}
#[test]
fn A2a1_json() {
    assert_parses_successfully_json(A2X1_json(a1_json()));
}
#[test]
fn A2a2_json() {
    assert_parses_successfully_json(A2X2_json(a2_json()));
}
#[test]
fn A2b1_json() {
    assert_parse_error_json(
        A2X1_json(b1_json()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS1::MyType")
            .help("`NS1::MyType` has not been declared")
            .build(),
    );
}
#[test]
fn A2b2_json() {
    assert_parse_error_json(
        A2X2_json(b2_json()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS1::MyType")
            .help("`NS1::MyType` has not been declared")
            .build(),
    );
}
#[test]
fn A2c_json() {
    assert_parse_error_json(
        A2X1_json(c_json()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS1::MyType")
            .help("`NS1::MyType` has not been declared")
            .build(),
    );
}
#[test]
fn A3a1_json() {
    assert_parse_error_json(
        A3X1_json(a1_json()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            .build(),
    );
}
#[test]
fn A3a2_json() {
    assert_parse_error_json(
        A3X2_json(a2_json()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            .build(),
    );
}
#[test]
fn A3b1_json() {
    assert_parse_error_json(
        A3X1_json(b1_json()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            .build(),
    );
}
#[test]
fn A3b2_json() {
    assert_parse_error_json(
        A3X2_json(b2_json()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            .build(),
    );
}
#[test]
fn A3c_json() {
    assert_parse_error_json(
        A3X1_json(c_json()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            .build(),
    );
}
#[test]
fn A3d1_json() {
    assert_parses_successfully_json(A3X1_json(d1_json()));
}
#[test]
fn A3d2_json() {
    assert_parses_successfully_json(A3X2_json(d2_json()));
}
#[test]
fn B1a1_json() {
    assert_parses_successfully_json(B1X1_json(a1_json()));
}
#[test]
fn B1a2_json() {
    assert_parses_successfully_json(B1X2_json(a2_json()));
}
#[test]
fn B1b1_json() {
    assert_parses_successfully_json(B1X1_json(b1_json()));
}
#[test]
fn B1b2_json() {
    assert_parses_successfully_json(B1X2_json(b2_json()));
}
#[test]
fn B1c_json() {
    assert_parse_error_json(
        B1X1_json(c_json()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: MyType")
            .help("neither `NS1::MyType` nor `MyType` refers to anything that has been declared")
            .build(),
    );
}
#[test]
fn B2a1_json() {
    assert_parses_successfully_json(B2X1_json(a1_json()));
}
#[test]
fn B2a2_json() {
    assert_parses_successfully_json(B2X2_json(a2_json()));
}
#[test]
fn B2b1_json() {
    assert_parse_error_json(
        B2X1_json(b1_json()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS1::MyType")
            .help("`NS1::MyType` has not been declared")
            .build(),
    );
}
#[test]
fn B2b2_json() {
    assert_parse_error_json(
        B2X2_json(b2_json()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS1::MyType")
            .help("`NS1::MyType` has not been declared")
            .build(),
    );
}
#[test]
fn B2c_json() {
    assert_parse_error_json(
        B2X1_json(c_json()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS1::MyType")
            .help("`NS1::MyType` has not been declared")
            .build(),
    );
}
#[test]
fn B3a1_json() {
    assert_parse_error_json(
        B3X1_json(a1_json()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            .build(),
    );
}
#[test]
fn B3a2_json() {
    assert_parse_error_json(
        B3X2_json(a2_json()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            .build(),
    );
}
#[test]
fn B3b1_json() {
    assert_parse_error_json(
        B3X1_json(b1_json()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            .build(),
    );
}
#[test]
fn B3b2_json() {
    assert_parse_error_json(
        B3X2_json(b2_json()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            .build(),
    );
}
#[test]
fn B3c_json() {
    assert_parse_error_json(
        B3X1_json(c_json()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            .build(),
    );
}
#[test]
fn B3d1_json() {
    assert_parses_successfully_json(B3X1_json(d1_json()));
}
#[test]
fn B3d2_json() {
    assert_parses_successfully_json(B3X2_json(d2_json()));
}
#[test]
fn C1a1_json() {
    assert_parses_successfully_json(C1X1_json(a1_json()));
}
#[test]
fn C1a2_json() {
    assert_parses_successfully_json(C1X2_json(a2_json()));
}
#[test]
fn C1b1_json() {
    assert_parses_successfully_json(C1X1_json(b1_json()));
}
#[test]
fn C1b2_json() {
    assert_parses_successfully_json(C1X2_json(b2_json()));
}
#[test]
fn C1c_json() {
    assert_parse_error_json(
        C1X1_json(c_json()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: MyType")
            .help("neither `NS1::MyType` nor `MyType` refers to anything that has been declared")
            .build(),
    );
}
#[test]
fn C2a1_json() {
    assert_parses_successfully_json(C2X1_json(a1_json()));
}
#[test]
fn C2a2_json() {
    assert_parses_successfully_json(C2X2_json(a2_json()));
}
#[test]
fn C2b1_json() {
    assert_parse_error_json(
        C2X1_json(b1_json()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS1::MyType")
            .help("`NS1::MyType` has not been declared")
            .build(),
    );
}
#[test]
fn C2b2_json() {
    assert_parse_error_json(
        C2X2_json(b2_json()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS1::MyType")
            .help("`NS1::MyType` has not been declared")
            .build(),
    );
}
#[test]
fn C2c_json() {
    assert_parse_error_json(
        C2X1_json(c_json()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS1::MyType")
            .help("`NS1::MyType` has not been declared")
            .build(),
    );
}
#[test]
fn C3a1_json() {
    assert_parse_error_json(
        C3X1_json(a1_json()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            .build(),
    );
}
#[test]
fn C3a2_json() {
    assert_parse_error_json(
        C3X2_json(a2_json()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            .build(),
    );
}
#[test]
fn C3b1_json() {
    assert_parse_error_json(
        C3X1_json(b1_json()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            .build(),
    );
}
#[test]
fn C3b2_json() {
    assert_parse_error_json(
        C3X2_json(b2_json()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            .build(),
    );
}
#[test]
fn C3c_json() {
    assert_parse_error_json(
        C3X1_json(c_json()),
        &ExpectedErrorMessageBuilder::error("failed to resolve type: NS2::MyType")
            .help("`NS2::MyType` has not been declared")
            .build(),
    );
}
#[test]
fn C3d1_json() {
    assert_parses_successfully_json(C3X1_json(d1_json()));
}
#[test]
fn C3d2_json() {
    assert_parses_successfully_json(C3X2_json(d2_json()));
}
