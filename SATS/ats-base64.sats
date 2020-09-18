
#define ATS_DYNLOADFLAG 0
#define ATS_EXTERN_PREFIX "ats-base64"

#include "share/atspre_staload.hats" // include template definitions

fn
  decode0
  {n: pos | n >= 4 && n == 4 * (n / 4)}{m:pos | m >= 1 + (n / 4) * 3}{l:agz}
  ( pf: !array_v( byte?, l, m) >> array_v( byte, l, m)
  | i: !string(n)
  , i_sz: size_t(n)
  , out: ptr l
  , out_sz: size_t(m)
  ): (bool, [m1: nat | m1 <= m] size_t(m1))
  
fn
  decode1
  {n:pos | n >= 4 && n == 4 * (n / 4)}
  ( i: string(n)
  , i_sz: size_t(n)
  ):
  Option_vt( [m:pos][l:agz] @( arrayptr(byte,l,m) , size_t(m), [m1:pos] size_t(m1))) (* result can contain NULL-chars *)
  
fn
  encode0
  {n: pos}{m:pos | m >= 1 + (n / 3) * 4 + 4 * bool2int((n - ((n / 3) * 3)) > 0) }{l:agz}
  ( o_pf: !array_v(byte?, l, m) >> array_v( byte, l, m)
  | i: &(@[byte][n])
  , i_sz: size_t(n)
  , o: ptr l
  , o_sz: size_t(m)
  ): void
  
fn
  encode1
  {n: pos}
  ( i: &(@[byte][n])
  , i_sz: size_t(n)
  ):
  [m:nat][m1:nat][l:agz]
  ( strnptr(l,m)
  , size_t(m1)
  )
  
