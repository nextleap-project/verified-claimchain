module Spec.Claim.Metadata

open FStar.Seq
open SkipList2.Statement
open SkipList2.Insertion2
open SkipList2.Properties
open SkipList2.Search
open Spec.Claim.Keys
open Spec.Claim.Common

type indentifier =
    |InitIndent : source: string -> identifier : string -> indentifier

type metadata =
    |InitMetadata:
        screenName: option string ->
        realName: option string ->
        identifiers: option (list indentifier) ->
        keys: cryptoKeyEnt ->
        hashMetadata: bytes
        {
        hashMetadata =
            (let c1 = toBytes screenName in
            let c2 = toBytes realName in
            let c3 = concat c1 c2 in
            let c4 = toBytes identifiers in
            let c5 = concat c3 c4 in
            let c6 = toBytes keys in
            let c7 = concat c5 c6 in 
            hash c7)
        } -> metadata 


val getKeys: meta: metadata -> Tot cryptoKeyEnt
let getKeys meta = 
    meta.keys
