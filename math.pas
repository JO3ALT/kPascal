(* math.pas
   Integer-only approximations for Pascal/0 extension.
   Conventions:
   - SCALE = 10000 (fixed-point 1.0 = 10000)
   - sin/cos/tan input: degrees (integer), output: fixed-point
   - asin/acos output: degrees (integer), input: fixed-point
   - ln/log input: positive integer, output: fixed-point
*)

function m_abs(x: integer): integer;
begin
  if x < 0 then
    m_abs := -x
  else
    m_abs := x
end;

function m_div(a: integer; b: integer): integer;
var
  ua: integer;
  ub: integer;
  q: integer;
  t: integer;
  m: integer;
  neg: integer;
begin
  if b = 0 then
    m_div := 0
  else
    begin
      neg := 0;
      ua := a;
      ub := b;
      if ua < 0 then
        begin
          ua := -ua;
          neg := 1 - neg
        end;
      if ub < 0 then
        begin
          ub := -ub;
          neg := 1 - neg
        end;

      q := 0;
      while ua >= ub do
        begin
          t := ub;
          m := 1;
          while t + t <= ua do
            begin
              t := t + t;
              m := m + m
            end;
          ua := ua - t;
          q := q + m
        end;

      if neg <> 0 then
        m_div := -q
      else
        m_div := q
    end
end;

function m_sin90(d: integer): integer;
var
  num: integer;
  den: integer;
begin
  (* Bhaskara I, d in [0..180], best near [0..90] with symmetry *)
  num := 16 * d * (180 - d);
  den := 40500 - d * (180 - d);
  if den = 0 then
    m_sin90 := 0
  else
    m_sin90 := m_div(num * 10000, den)
end;

function sqrt(x: integer): integer;
var
  lo: integer;
  hi: integer;
  mid: integer;
  ans: integer;
  sq: integer;
begin
  if x <= 0 then
    sqrt := 0
  else
    begin
      lo := 0;
      hi := x;
      if hi > 46340 then
        hi := 46340;
      ans := 0;
      while lo <= hi do
        begin
          mid := m_div(lo + hi, 2);
          sq := mid * mid;
          if sq <= x then
            begin
              ans := mid;
              lo := mid + 1
            end
          else
            hi := mid - 1
        end;
      sqrt := ans
    end
end;

function sin(a: integer): integer;
var
  d: integer;
  s: integer;
begin
  d := a;
  while d < 0 do d := d + 360;
  while d >= 360 do d := d - 360;
  s := 1;
  if d > 180 then
    begin
      d := d - 180;
      s := -1
    end;
  if d > 90 then
    d := 180 - d;
  sin := s * m_sin90(d)
end;

function cos(a: integer): integer;
begin
  cos := sin(90 - a)
end;

function tan(a: integer): integer;
var
  c: integer;
begin
  c := cos(a);
  if c = 0 then
    tan := 0
  else
    tan := m_div(sin(a) * 10000, c)
end;

function asin(v: integer): integer;
var
  i: integer;
  besti: integer;
  beste: integer;
  e: integer;
begin
  if v >= 10000 then
    asin := 90
  else if v <= -10000 then
    asin := -90
  else
    begin
      besti := 0;
      beste := 2147483647;
      i := -90;
      while i <= 90 do
        begin
          e := m_abs(sin(i) - v);
          if e < beste then
            begin
              beste := e;
              besti := i
            end;
          i := i + 1
        end;
      asin := besti
    end
end;

function acos(v: integer): integer;
begin
  acos := 90 - asin(v)
end;

function atan(v: integer): integer;
var
  i: integer;
  besti: integer;
  beste: integer;
  e: integer;
  av: integer;
  s: integer;
begin
  s := 1;
  av := v;
  if av < 0 then
    begin
      av := -av;
      s := -1
    end;
  besti := 0;
  beste := 2147483647;
  i := 0;
  while i <= 89 do
    begin
      e := m_abs(tan(i) - av);
      if e < beste then
        begin
          beste := e;
          besti := i
        end;
      i := i + 1
    end;
  atan := s * besti
end;

function ln(x: integer): integer;
var
  xn: integer;
  y: integer;
  y2: integer;
  term: integer;
  sum: integer;
  k: integer;
  n: integer;
  i: integer;
begin
  if x <= 0 then
    ln := 0
  else
    begin
      xn := x * 10000;
      k := 0;
      while xn > 2 * 10000 do
        begin
          xn := m_div(xn, 2);
          k := k + 1
        end;
      while xn < 10000 do
        begin
          xn := xn * 2;
          k := k - 1
        end;

      y := m_div((xn - 10000) * 10000, xn + 10000);
      y2 := m_div(y * y, 10000);
      term := y;
      sum := term;
      n := 3;
      i := 0;
      while i < 6 do
        begin
          term := m_div(term * y2, 10000);
          sum := sum + m_div(term, n);
          n := n + 2;
          i := i + 1
        end;
      ln := 2 * sum + k * 6931
    end
end;

function log(x: integer): integer;
begin
  log := m_div(ln(x) * 10000, 23026)
end;
