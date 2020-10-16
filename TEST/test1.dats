#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0

staload B64="./../SATS/ats-base64.sats"

extern fn
  memcmp
  {n, n1, n2: nat | n2 <= n && n2 <= n1}
  {a:t0ype}{b:t0ype}
  {l,l1:agz}
  ( !array_v(a, l, n)
  , !array_v(b, l1, n1)
  | ptr l
  , ptr l1
  , size_t(n2)
  ): int = "mac#"

extern castfn
  i2b
  ( i: int
  ):<> byte

implement main0() = {
  val encoded = "+gEWAAUBEQACASsAABlALAAA2wAtAAC0Dy4AAMcmzuib"
  var reference = @[byte]( i2b 0xfa, i2b 0x01, i2b 0x16, i2b 0x00, i2b 0x05
                         , i2b 0x01, i2b 0x11, i2b 0x00, i2b 0x02, i2b 0x01
                         , i2b 0x2b, i2b 0x00, i2b 0x00, i2b 0x19, i2b 0x40
                         , i2b 0x2c, i2b 0x00, i2b 0x00, i2b 0xdb, i2b 0x00
                         , i2b 0x2d, i2b 0x00, i2b 0x00, i2b 0xb4, i2b 0x0f
                         , i2b 0x2e, i2b 0x00, i2b 0x00, i2b 0xc7, i2b 0x26
                         , i2b 0xce, i2b 0xe8, i2b 0x9b
                         )
  val- ~Some_vt(tuple) = $B64.decode1( encoded, length encoded)
  val ( decoded, cap, sz) = tuple
  val () = assertloc( sz = i2sz 33)
  val (arr_pf | arr) = arrayptr_takeout_viewptr( decoded)
  val () = assertloc( memcmp( view@reference, arr_pf | addr@reference, arr, sz) = 0)
  prval () = arrayptr_addback( arr_pf | decoded)
  val () = arrayptr_free decoded
}