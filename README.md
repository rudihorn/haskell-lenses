# Demo Schema

The examples contain a simple schema for the example tables from the Bohannon
PODS 2016 paper located in `schema.sql`. These are two tables `albums` and
`tracks`. By default the database expects a database called `links` with user
`links` and password `links`.

# Running examples

The easiest way to run examples is to use `ghci`. Calling `./run.sh` will start
GHCI with the required extensions needed for lenses. The example code is located
in `Scratch.hs` and can be loaded using the `:l Scratch` pragma.

## Example functions

`test_ex : lens -> records` queries a lens.

`test_put : lens -> records -> unit` updates a lens with the supplied records.

`test_put_debug : lens -> records -> unit` returns how it would update the database, but does not actually make changes.

## Filling database

The database can be filled with information 

```
test_put albums unchangedAlbums
test_put tracks unchangedTracks
```

## PODS example

The PODS example is defined with the following lenses and primitive tables:

```
type Albums = '[ '("album", String), '("quantity", Int)]

albums = prim @"albums" @Albums
  @'[ '["album"] --> '["quantity"]]

type Tracks = '[
  '("track", String),
  '("date", Int),
  '("rating", Int),
  '("album", String)]

tracks = prim @"tracks" @Tracks
  @'[ '["track"] --> '["date", "rating"]]

tracks1 = join tracks albums
tracks2 = dropl @'[ '("date", 'P.Int 2020)] @'["track"] tracks1
tracks3 = select (#quantity !> di 2) tracks2
```

The view can be fetched using:

```
test_get tracks3
```

And the example update can be performed by:

```
test_put tracks3 examplePut 
```
