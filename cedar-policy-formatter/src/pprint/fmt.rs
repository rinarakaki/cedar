/*
 * Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use std::collections::BTreeMap;

use miette::{miette, Result, WrapErr};

use cedar_policy_core::ast::PolicySet;
use cedar_policy_core::parser::parse_policyset;
use cedar_policy_core::parser::{err::ParseErrors, text_to_cst::parse_policies};
use smol_str::ToSmolStr;

use crate::token::get_comment;

use super::lexer::get_token_stream;
use super::utils::remove_empty_lines;

use super::config::{self, Config};
use super::doc::*;

fn tree_to_pretty<T: Doc>(t: &T, context: &mut config::Context<'_>) -> Result<String> {
    let mut w = Vec::new();
    let config = context.config;
    let doc = t.to_doc(context);
    doc.ok_or(miette!("failed to produce doc"))?
        .render(config.line_width, &mut w)
        .map_err(|err| miette!(format!("failed to render doc: {err}")))?;
    String::from_utf8(w)
        .map_err(|err| miette!(format!("failed to convert rendered doc to string: {err}")))
}

fn soundness_check(ps: &str, ast: &PolicySet) -> Result<()> {
    let formatted_ast = parse_policyset(ps).wrap_err("formatter produces invalid policies")?;
    let (formatted_policies, policies) = (
        formatted_ast
            .policies()
            .map(|p| (p.id().to_smolstr(), p))
            .collect::<BTreeMap<_, _>>(),
        ast.policies()
            .map(|p| (p.id().to_smolstr(), p))
            .collect::<BTreeMap<_, _>>(),
    );

    if formatted_policies.len() != policies.len() {
        return Err(miette!("missing formatted policies"));
    }
    for ((f_p_id, f_p), (p_id, p)) in formatted_policies.into_iter().zip(policies.into_iter()) {
        let (f_anno, anno) = (
            f_p.annotations()
                .map(|(k, v)| (k, &v.val))
                .collect::<std::collections::BTreeMap<_, _>>(),
            p.annotations()
                .map(|(k, v)| (k, &v.val))
                .collect::<std::collections::BTreeMap<_, _>>(),
        );
        if !(f_p_id == p_id
            && f_anno == anno
            && f_p.effect() == p.effect()
            && f_p.principal_constraint() == p.principal_constraint()
            && f_p.action_constraint() == p.action_constraint()
            && f_p.resource_constraint() == p.resource_constraint()
            && f_p
                .non_head_constraints()
                .eq_shape(p.non_head_constraints()))
        {
            return Err(miette!(
                "policies differ in policy ids or meaning or annotations:\noriginal: {p}\nformatted: {f_p}"
            ));
        }
    }
    Ok(())
}

pub fn policies_str_to_pretty(ps: &str, config: &Config) -> Result<String> {
    let cst = parse_policies(ps).wrap_err("cannot parse input policies to CSTs")?;
    let mut errs = ParseErrors::new();
    let ast = cst
        .to_policyset(&mut errs)
        .ok_or(errs)
        .wrap_err("cannot parse input policies to ASTs")?;
    let tokens = get_token_stream(ps).ok_or(miette!("cannot get token stream"))?;
    let end_comment_str = ps
        .get(
            tokens
                .last()
                .ok_or(miette!("token stream is empty"))?
                .span
                .end..,
        )
        .ok_or(miette!("cannot get ending comment string"))?;
    let mut context = config::Context { config, tokens };
    let mut formatted_policies = cst
        .as_inner()
        .ok_or(miette!("fail to get input policy CST"))?
        .0
        .iter()
        .map(|p| Ok(remove_empty_lines(tree_to_pretty(p, &mut context)?.trim())))
        .collect::<Result<Vec<String>>>()?
        .join("\n\n");
    // handle comment at the end of a policyset
    let (trailing_comment, end_comment) = match end_comment_str.split_once('\n') {
        Some((f, r)) => (get_comment(f), get_comment(r)),
        None => (get_comment(end_comment_str), String::new()),
    };
    match (trailing_comment.as_ref(), end_comment.as_ref()) {
        ("", "") => {}
        (_, "") => {
            formatted_policies.push(' ');
            formatted_policies.push_str(&trailing_comment);
        }
        ("", _) => {
            formatted_policies.push('\n');
            formatted_policies.push_str(&end_comment);
        }
        _ => {
            formatted_policies.push(' ');
            formatted_policies.push_str(&trailing_comment);
            formatted_policies.push_str(&end_comment);
        }
    };
    // add soundness check to make sure formatting doesn't alter policy ASTs
    soundness_check(&formatted_policies, &ast)?;
    Ok(formatted_policies)
}

#[cfg(test)]
mod tests {
    use super::*;
    const TEST_CONFIG: &Config = &Config {
        line_width: 40,
        indent_width: 2,
    };

    #[test]
    fn trivial_permit() {
        let policy = r#"permit (principal, action, resource);"#;
        assert_eq!(policies_str_to_pretty(policy, TEST_CONFIG).unwrap(), policy);
    }

    #[test]
    fn trivial_forbid() {
        let policy = r#"forbid (principal, action, resource);"#;
        assert_eq!(policies_str_to_pretty(policy, TEST_CONFIG).unwrap(), policy);
    }

    #[test]
    fn action_in_set() {
        let policy = r#"permit (
        principal in UserGroup::"abc",
        action in [Action::"viewPhoto", Action::"viewComments"],
        resource in Album::"one"
      );"#;
        assert_eq!(
            policies_str_to_pretty(policy, TEST_CONFIG).unwrap(),
            r#"permit (
  principal in UserGroup::"abc",
  action in
    [Action::"viewPhoto",
     Action::"viewComments"],
  resource in Album::"one"
);"#
        );
    }

    #[test]
    fn test_soundness_check() {
        let p1 = r#"permit (principal, action, resource)
        when { "
        
        a
        " };"#;
        let p2 = r#"permit (principal, action, resource)
        when { "
        a
        " };"#;
        assert!(soundness_check(p2, &parse_policyset(p1).unwrap()).is_err());

        let p1 = r#"
        permit (principal, action, resource)
        when { "a"};
        permit (principal, action, resource)
        when { "
        
        a
        " };"#;
        let p2 = r#"
        permit (principal, action, resource)
        when { "
        a
        " };
        permit (principal, action, resource)
        when { "a"};"#;
        assert!(soundness_check(p2, &parse_policyset(p1).unwrap()).is_err());

        let p1 = r#"
        permit (principal, action, resource)
        when { "a"   };
        permit (principal, action, resource)
        when { "b" };"#;
        let p2 = r#"
        permit (principal, action, resource)
        when { "a" };
        permit (principal, action, resource)
        when { "b"};"#;
        assert!(soundness_check(p2, &parse_policyset(p1).unwrap()).is_ok());
    }

    #[test]
    fn test_format_files() {
        use std::fs::read_to_string;
        use std::path::Path;

        let config = Config {
            line_width: 80,
            indent_width: 2,
        };
        let dir_path = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests");
        let pairs = vec![
            ("test.cedar", "test_formatted.cedar"),
            ("policies.cedar", "policies_formatted.cedar"),
            ("is_policies.cedar", "is_policies_formatted.cedar"),
        ];
        for (pf, ef) in pairs {
            // editors or cargo run try to append a newline at the end of files
            // we should remove them for equality testing
            assert_eq!(
                policies_str_to_pretty(&read_to_string(dir_path.join(pf)).unwrap(), &config)
                    .unwrap()
                    .trim_end_matches('\n'),
                read_to_string(dir_path.join(ef))
                    .unwrap()
                    .trim_end_matches('\n')
            );
        }
    }
}
