polyvariadic-generic-deriving
=============================

This is a Haskell generic programming library like `GHC.Generics` but with
support for any number of `*` parameters

It's largely another take on Hesselink's technique in his master's thesis, but
with some of the newer GHC features. As far as I know, the ability to represent
type applications (often referred to as "composition") in addition to
polyvariadism is unique. I'm only claiming partial support for that, btw: it's
working for the few small examples I have so far, but that at least includes
non-regular and mutually recursive data types with two parameters.

I use an ugly workaround to fake polykinded values -- it is defined in
`Data.PVGD.W`. It unfortunatlely must be exposed to the user, but it really
isn't that bad. The user just has to occasionally use one of `asW0`, `asW1`,
`asW2`, etc instead of `$` based on the kinds.

I use an ever uglier trick to recover useful type inference. This is a
workaround for the fact that GADTs cannot be promoted. It unfortunately invades
any higher-kinded type class that should ever have a generic definition.

There's more discussion in the source files.

See `examples/Examples.hs`. I currently only have two generic definitions, one
for decidable equality and one for a polyvariadic covariant map extension (ie
generalized fmap). The latter is more interesting and defined in
`Data.PVGD.Covariant`.
