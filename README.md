# parsing

A library for parsing expressions.

It provides an interface for parsers via the `Parser` trait. The results of
parsing are represented by the `ParseResult` type. A blanket implementation of
`Parser` is provided for all functions that input a `&str` and return a
`ParseResult`.

Functions that can augment parsers in various ways are also provided. For
example, `one_or_more` takes a parser and applies it successively to the input,
at least one time. `combination` combines applies two parsers successively and
returns the results of both, provided that both of them succeed in parsing.

Build the documentation for more info.
