
{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             MultiParamTypeClasses, FlexibleInstances, PolyKinds,
             FlexibleContexts, UndecidableInstances, ConstraintKinds,
             ScopedTypeVariables, TypeInType, TypeOperators, StandaloneDeriving,
             AllowAmbiguousTypes, TypeApplications, OverloadedStrings #-}


module TicketSystem where

import Database.PostgreSQL.Simple(query_, connect, defaultConnectInfo, connectDatabase, connectUser, connectPassword, Connection)

import FunDep
import Lens (prim, join, select, dropl, debug)
import Lens.Database.Base (LensGet, get)
import LensPut (put, put_wif)
import Lens.Predicate.Hybrid
import Lens.Database.Postgres (PostgresDatabase)
import Lens.Database.Table (setup)
import Lens.Record.Sorted (RecordsSet, rows)

import qualified Lens.Predicate.Base as P


type Event = '[ '("event_id", Int), '("event_name", String) ]
events = prim @"events" @Event @'[ '["event_id"] --> '["event_name"]]

type Reservation = '[ '("res_id", Int), '("event_id", Int) ]
reservations = prim @"reservations" @Reservation @'[ '["res_id"] --> '["event_id"] ]

type Ticket = '[ '("res_id", Int), '("email", String) ]
tickets = prim @"tickets" @Ticket @'[]

type User = '[ '("email", String), '("title", String), '("name", String) ]
users = prim @"users" @User @'[ '["email"] --> '["title", "name"]]

type DefaultUser = '[ '("name", 'P.String "<unknown>"), '("title", 'P.String "Mx.")]

users_dr = dropl @DefaultUser @'["email"] users

joined = join (join tickets users) (join reservations events)


db_connect = connect defaultConnectInfo{
    connectDatabase = "links",
    connectUser = "links",
    connectPassword = "links"
  }

do_setup =
  do conn <- db_connect
     setup conn joined

run =
  do conn <- db_connect
     res <- get conn joined
     return res

res_view_ext id =
  select (#res_id != di id) (join tickets users)


res_view id =
  select (#res_id != di id) (join tickets users_dr)

user email =
  select (#email != ds email) users

set_user conn email title name =
  do let view = user email
     put conn view $ rows [(email, title, name)]

set_emails conn id emails =
  put conn (res_view id) $
    rows (map (\email -> (id, email)) emails)


-- conn <- db_connect

-- put conn (res_view 1) $ rows [(1, "me@example.com"), (1, "max@mail.com")]
-- get conn $ res_view 1
-- get conn $ res_view_ext 1

-- set_user conn "max@mail.com" "Mr." "Max"

-- put conn (res_view 2) $ rows [(2, "me@example.com"), (2, "max@mail.com")]
