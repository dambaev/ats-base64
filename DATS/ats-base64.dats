
#define ATS_DYNLOADFLAG 0
#define ATS_EXTERN_PREFIX "ats-base64"

#include "share/atspre_staload.hats" // include template definitions

staload "./../SATS/ats-base64.sats"
staload UN="prelude/SATS/unsafe.sats"

extern
castfn
  string2bytes
  {n:nat}
  ( s: string(n)
  , sz: size_t(n)
  ):
  [l:agz]
  ( bytes_v(l,n)
  , (bytes_v(l,n) | ptr l) -<> void
  | ptr l
  )
  


extern
castfn
  bytes2strnptr
  {l:agz}{n:nat}
  ( pf: b0ytes_v(l,n)
  , free_pf: mfree_gc_v(l)
  | i: ptr l
  , i_sz: size_t(n)
  ): strnptr(l, n)
  
implement encode1( i, i_sz) = (out, out_sz) where {
  val out_sz = (i_sz / i2sz(3)) * 4 + 4 * bool2int( (i_sz - ((i_sz / i2sz(3)) * 3)) > 0) + 1
  val (out_pf, out_free_pf | out_ptr) = malloc_gc( out_sz)
  val () = encode0( out_pf | i, i_sz, out_ptr, out_sz)
  val out = bytes2strnptr( out_pf, out_free_pf | out_ptr, out_sz)
}

implement decode1( i, i_sz) = let
  val pad_sz =
    if i[ i_sz - 1] <> '='
    then 0
    else
      if i[ i_sz - 2] <> '='
      then 3
      else 2
  val out_sz = 1 + (i_sz / i2sz(4)) * 3
  val (out_pf, out_free_pf | out_ptr) = malloc_gc( out_sz)
  val (isdecoded, decoded_sz) = decode0( out_pf | i, i_sz, out_ptr, out_sz)
in
  if not isdecoded
  then None_vt() where {
    val () = array_ptr_free( out_pf, out_free_pf | out_ptr)
  }
  else Some_vt( @(arr, out_sz, decoded_sz)) where {
    val () = assertloc( decoded_sz > 0)
    val arr = arrayptr_encode( out_pf, out_free_pf | out_ptr)
  }
end
  
extern
prfun
  array_v_unnil_nz
  {a:t0ype}{l:addr}{n:nat}
  ( pf: array_v(a?, l, n)
  ): array_v(a, l, n)
 
implement encode0{n}{m}( o_pf | i, i_sz, o, o_sz) = {
  val (b64_table_pf, b64_table_free_pf | base64_table) = string2bytes("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/", i2sz(64))
  fun
    loop
    {iidx: nat | iidx <= n}{oidx: nat | oidx <= m}{l:agz}
    .<n-iidx, m-oidx>.
    ( pf: !bytes_v(l, 64)
    | iidx: size_t(iidx)
    , oidx: size_t(oidx)
    , i: &(@[byte][n])
    , o: &(@[byte?][m])
    , base64_table: ptr l
    ): void =
      if iidx + 3 <= i_sz
      then loop( pf | iidx + 3, oidx + 4, i, o, base64_table) where {
        val () = assertloc( oidx + 4 <= o_sz)
        (* 0 *)
        val idx = g1ofg0( $UN.cast{uint0}(i[ iidx]) >> 2)
        val () = assertloc( idx < 64)
        val () = o[oidx] := array_get_at_guint( !base64_table, idx)
        (* 1 *)
        val idx = g1ofg0(( ($UN.cast{uint0}(i[ iidx]) land 0x03u) << 4) lor (($UN.cast{uint0} i[iidx + 1]) >> 4))
        val () = assertloc( idx < 64)
        val () = o[oidx + 1] := array_get_at_guint( !base64_table, idx)
        (* 2 *)
        val idx = g1ofg0(( ($UN.cast{uint0}(i[ iidx + 1]) land 0x0fu) << 2) lor (($UN.cast{uint0} i[iidx + 2]) >> 6))
        val () = assertloc( idx < 64)
        val () = o[oidx + 2] := array_get_at_guint( !base64_table, idx)
        (* 3 *)
        val idx = g1ofg0( ($UN.cast{uint0}(i[ iidx + 2]) land 0x3fu))
        val () = assertloc( idx < 64)
        val () = o[oidx + 3] := array_get_at_guint( !base64_table, idx)

      } else
      if i_sz - iidx = 0
      then ()
      else {
        val () = assertloc( o_sz - oidx = 5) (* 4 + NULL*)
        val () = o[oidx + 4] := $UN.cast{byte}0x00
        val () = o[oidx + 3] := $UN.cast{byte}'='
        val idx = g1ofg0( $UN.cast{uint0}(i[ iidx]) >> 2)
        val () = assertloc( idx < 64)
        val () = o[oidx] := array_get_at_guint( !base64_table, idx)
        val () =
          if iidx + 1 = i_sz
          then {
            val idx = g1ofg0( ($UN.cast{uint0}(i[ iidx]) land 0x03u) << 4)
            val () = assertloc( idx < 64)
            val () = o[oidx + 1] := array_get_at_guint( !base64_table, idx)
            val () = o[oidx + 2] := $UN.cast{byte}'='
          } else {
            val idx = g1ofg0(( ($UN.cast{uint0}(i[ iidx]) land 0x03u) << 4) lor (($UN.cast{uint0} i[iidx + 1]) >> 4))
            val () = assertloc( idx < 64)
            val () = o[oidx + 1] := array_get_at_guint( !base64_table, idx)
            val idx = g1ofg0(( ($UN.cast{uint0}(i[ iidx + 1]) land 0x0fu) << 2))
            val () = assertloc( idx < 64)
            val () = o[oidx + 2] := array_get_at_guint( !base64_table, idx)
          }
      }
  val () = loop( b64_table_pf | i2sz(0), i2sz(0), i, !o, base64_table)
  prval () = b64_table_free_pf( b64_table_pf | base64_table)
  prval () = o_pf := array_v_unnil_nz( o_pf)
}

implement decode0{n}{m}( pf | i, i_sz, o, o_sz) = (flag, decoded_sz) where {
  var d64_table = @[uint]( 0u,  0u,  0u,  0u,  0u,  0u,  0u,  0u,  0u,  0u,  0u,  0u,
0u,  0u,  0u,  0u,  0u,  0u,  0u,  0u,  0u,  0u,  0u,  0u,  0u,  0u,  0u,  0u,  0u,  0u,  0u,  0u,
0u,  0u,  0u,  0u,  0u,  0u,  0u,  0u,  0u,  0u,  0u, 62u, 63u, 62u, 62u, 63u, 52u, 53u, 54u, 55u,
56u, 57u, 58u, 59u, 60u, 61u,  0u,  0u,  0u,  0u,  0u,  0u,  0u,  0u,  1u,  2u,  3u,  4u,  5u,  6u,
7u,  8u,  9u, 10u, 11u, 12u, 13u, 14u, 15u, 16u, 17u, 18u, 19u, 20u, 21u, 22u, 23u, 24u, 25u,  0u,
0u,  0u,  0u, 63u,  0u, 26u, 27u, 28u, 29u, 30u, 31u, 32u, 33u, 34u, 35u, 36u, 37u, 38u, 39u, 40u,
41u, 42u, 43u, 44u, 45u, 46u, 47u, 48u, 49u, 50u, 51u)
  val pad = $UN.cast{char}(i[ i_sz - 1 ]) = '='
  fun
    loop
    {iidx: nat | iidx <= n}{oidx: nat | oidx <= m}
    .<n - iidx>.
    ( iidx: size_t(iidx)
    , oidx: size_t(oidx)
    , i: &(@[byte][n])
    , o: &(@[byte?][m])
    , d64_table: &(@[uint][123])
    ): (bool, sizeLte(m)) = 
      ifcase
        (* end of output  *)
      | oidx >= o_sz => (false, oidx) where { prval () = prop_verify{ oidx >= m}() }
        (* end of input *)
      | iidx + 4 > i_sz => (true, oidx) where {
        prval () = prop_verify{ iidx + 4 > n}() 
        val () = o[oidx] := $UN.cast{byte}'\x0'
      }
        (* end of output  *)
      | oidx + 3 > o_sz => (true, oidx) where { prval () = prop_verify{ oidx + 3 > m}() }
      | _ => let
          prval () = prop_verify{iidx + 4 <= n && oidx + 3 <= m}()
          val idx0 = g1ofg0( $UN.cast{uint0}(array_get_at_guint( i, iidx)))
          val idx1 = g1ofg0( $UN.cast{uint0}(array_get_at_guint( i, iidx + 1)))
          val idx2 = g1ofg0( $UN.cast{uint0}(array_get_at_guint( i, iidx + 2)))
          val idx3 = g1ofg0( $UN.cast{uint0}(array_get_at_guint( i, iidx + 3)))
        in ifcase
          | idx0 >= 123 => (false, oidx)
          | idx1 >= 123 => (false, oidx)
          | idx2 >= 123 => (false, oidx)
          | idx3 >= 123 => (false, oidx)
            (* indexes are in bound *)
          | iidx + 4 = i_sz && pad => let
              val n:uint0 = (   (d64_table[idx0] << 18)
                            lor (d64_table[idx1] << 12)
                            )
              val () = o[ oidx ] := $UN.cast{byte}(n >> 16)
            in
              if '=' = $UN.cast{char}idx2
              then loop( iidx + 4, oidx + 1, i, o, d64_table)
              else loop( iidx + 4, oidx + 2, i, o, d64_table) where {
                  val n:uint0 = n lor (d64_table[idx2] << 6)
                  val () = o[ oidx + 1] := $UN.cast{byte}((n >> 8) land g0ofg1(0xffu))
              }
            end
          | _ => loop( iidx + 4, oidx + 3, i, o, d64_table) where {
            val n:uint0 = (( d64_table[idx0] << 18)
                          lor (d64_table[idx1] << 12)
                          lor (d64_table[idx2] << 6)
                          lor (d64_table[idx3])
                          )
            val () = o[ oidx ] := $UN.cast{byte}(n >> 16)
            val () = o[ oidx + 1] := $UN.cast{byte}((n >> 8) land g0ofg1(0xffu))
            val () = o[ oidx + 2] := $UN.cast{byte}(n land 0xffu)
          }
        end
  val (i_pf, i_free_pf | i_ptr) = string2bytes( i, i_sz)
  val (flag, decoded_sz) = loop( i2sz(0), i2sz(0), !i_ptr, !o, d64_table)
  prval () = i_free_pf( i_pf | i_ptr)
  prval () = pf := array_v_unnil_nz( pf)
}