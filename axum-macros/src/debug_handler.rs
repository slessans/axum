<<<<<<< HEAD
use crate::attr_parsing::second;
use proc_macro2::TokenStream;
use quote::quote;
use syn::{parse_quote, FnArg, ItemFn, Type};

use self::attr::Attrs;
use self::specializer::Specializer;

mod attr;
mod specializer;
=======
use std::collections::HashSet;

use crate::{
    attr_parsing::{parse_assignment_attribute, second},
    with_position::{Position, WithPosition},
};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote, quote_spanned};
use syn::{parse::Parse, parse_quote, spanned::Spanned, FnArg, ItemFn, Token, Type};
>>>>>>> main

pub(crate) fn expand(attr: Attrs, item_fn: ItemFn) -> TokenStream {
    let Attrs {
        body_ty,
        state_ty,
        with_tys,
    } = attr;
    let body_ty = body_ty
        .map(second)
        .unwrap_or_else(|| parse_quote!(axum::body::Body));
    let mut state_ty = state_ty.map(second);
    if state_ty.is_none() {
        state_ty = state_type_from_args(&item_fn);
    }
    let state_ty = state_ty.unwrap_or_else(|| syn::parse_quote!(()));

    // these checks don't require the specializer, so we can generate code for them regardless
    // of whether we can successfully create one
    let check_extractor_count = check_extractor_count(&item_fn);
    let check_path_extractor = check_path_extractor(&item_fn);

<<<<<<< HEAD
    // If the function is generic and an improper `with` statement was provided to the macro, we can't
    // reliably check its inputs or outputs. This will result in an error. We skip those checks to avoid
    // unhelpful additional compiler errors.
    let specializer_checks = match Specializer::new(with_tys, item_fn.clone(), body_ty, state_ty) {
        Ok(specializer) => {
            let check_output_impls_into_response =
                specializer.generate_check_output_impls_into_response();
            let check_inputs_impls_from_request =
                specializer.generate_check_inputs_impl_from_request();
            let check_future_send = specializer.generate_check_output_future_send();

            quote! {
                #check_output_impls_into_response
                #check_inputs_impls_from_request
                #check_future_send
            }
        }
        Err(err) => err.into_compile_error(),
=======
    // If the function is generic, we can't reliably check its inputs or whether the future it
    // returns is `Send`. Skip those checks to avoid unhelpful additional compiler errors.
    let check_inputs_and_future_send = if item_fn.sig.generics.params.is_empty() {
        let mut err = None;

        if state_ty.is_none() {
            let state_types_from_args = state_types_from_args(&item_fn);

            #[allow(clippy::comparison_chain)]
            if state_types_from_args.len() == 1 {
                state_ty = state_types_from_args.into_iter().next();
            } else if state_types_from_args.len() > 1 {
                err = Some(
                    syn::Error::new(
                        Span::call_site(),
                        "can't infer state type, please add set it explicitly, as in \
                         `#[debug_handler(state = MyStateType)]`",
                    )
                    .into_compile_error(),
                );
            }
        }

        err.unwrap_or_else(|| {
            let state_ty = state_ty.unwrap_or_else(|| syn::parse_quote!(()));

            let check_inputs_impls_from_request =
                check_inputs_impls_from_request(&item_fn, &body_ty, state_ty);
            let check_future_send = check_future_send(&item_fn);

            quote! {
                #check_inputs_impls_from_request
                #check_future_send
            }
        })
    } else {
        syn::Error::new_spanned(
            &item_fn.sig.generics,
            "`#[axum_macros::debug_handler]` doesn't support generic functions",
        )
        .into_compile_error()
>>>>>>> main
    };

    quote! {
        #item_fn
        #check_extractor_count
        #check_path_extractor
        #specializer_checks
    }
}

fn check_extractor_count(item_fn: &ItemFn) -> Option<TokenStream> {
    let max_extractors = 16;
    if item_fn.sig.inputs.len() <= max_extractors {
        None
    } else {
        let error_message = format!(
            "Handlers cannot take more than {} arguments. \
            Use `(a, b): (ExtractorA, ExtractorA)` to further nest extractors",
            max_extractors,
        );
        let error = syn::Error::new_spanned(&item_fn.sig.inputs, error_message).to_compile_error();
        Some(error)
    }
}

fn extractor_idents(item_fn: &ItemFn) -> impl Iterator<Item = (usize, &syn::FnArg, &syn::Ident)> {
    item_fn
        .sig
        .inputs
        .iter()
        .enumerate()
        .filter_map(|(idx, fn_arg)| match fn_arg {
            FnArg::Receiver(_) => None,
            FnArg::Typed(pat_type) => {
                if let Type::Path(type_path) = &*pat_type.ty {
                    type_path
                        .path
                        .segments
                        .last()
                        .map(|segment| (idx, fn_arg, &segment.ident))
                } else {
                    None
                }
            }
        })
}

fn check_path_extractor(item_fn: &ItemFn) -> TokenStream {
    let path_extractors = extractor_idents(item_fn)
        .filter(|(_, _, ident)| *ident == "Path")
        .collect::<Vec<_>>();

    if path_extractors.len() > 1 {
        path_extractors
            .into_iter()
            .map(|(_, arg, _)| {
                syn::Error::new_spanned(
                    arg,
                    "Multiple parameters must be extracted with a tuple \
                    `Path<(_, _)>` or a struct `Path<YourParams>`, not by applying \
                    multiple `Path<_>` extractors",
                )
                .to_compile_error()
            })
            .collect()
    } else {
        quote! {}
    }
}

/// Given a signature like
///
/// ```skip
/// #[debug_handler]
/// async fn handler(
///     _: axum::extract::State<AppState>,
///     _: State<AppState>,
/// ) {}
/// ```
///
/// This will extract `AppState`.
///
/// Returns `None` if there are no `State` args or multiple of different types.
fn state_types_from_args(item_fn: &ItemFn) -> HashSet<Type> {
    let types = item_fn
        .sig
        .inputs
        .iter()
        .filter_map(|input| match input {
            FnArg::Receiver(_) => None,
            FnArg::Typed(pat_type) => Some(pat_type),
        })
        .map(|pat_type| &*pat_type.ty);
    crate::infer_state_types(types).collect()
}

#[test]
fn ui() {
    crate::run_ui_tests("debug_handler");
}
