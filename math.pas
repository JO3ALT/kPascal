function abs(x: float): float;
begin
  if x < 0.0 then
    abs := -x
  else
    abs := x
end;

function sqrt(x: float): float;
var
  g: float;
  i: integer;
begin
  if x <= 0.0 then
    begin
      sqrt := 0.0
    end
  else
    begin
      g := x;
      for i := 1 to 8 do
        g := (g + x / g) / 2.0;
	      sqrt := g
	    end
end;

function pow(x: float; n: integer): float;
var
  i: integer;
  e: integer;
  r: float;
begin
  if n = 0 then
    pow := 1.0
  else
    begin
      r := 1.0;
      e := n;
      if e < 0 then
        e := -e;
      i := 1;
      while i <= e do
        begin
          r := r * x;
          i := i + 1
        end;
      if n < 0 then
        pow := 1.0 / r
      else
        pow := r
    end
end;

function sin(x: float): float;
var
  x2: float;
  x3: float;
  x5: float;
  x7: float;
begin
  x2 := x * x;
  x3 := x * x2;
  x5 := x3 * x2;
  x7 := x5 * x2;
  sin := x - x3 / 6.0 + x5 / 120.0 - x7 / 5040.0
end;

function cos(x: float): float;
var
  x2: float;
  x4: float;
  x6: float;
begin
  x2 := x * x;
  x4 := x2 * x2;
  x6 := x4 * x2;
  cos := 1.0 - x2 / 2.0 + x4 / 24.0 - x6 / 720.0
end;

function f_trunc(x: float): float;
begin
  f_trunc := Float(Trunc(x))
end;

function f_round(x: float): float;
begin
  f_round := Float(Round(x))
end;

function floor(x: float): float;
var
  t: integer;
  tf: float;
begin
  t := Trunc(x);
  tf := Float(t);
  if x < 0.0 then
    begin
      if x <> tf then
        floor := Float(t - 1)
      else
        floor := tf
    end
  else
    floor := tf
end;

function ceil(x: float): float;
var
  t: integer;
  tf: float;
begin
  t := Trunc(x);
  tf := Float(t);
  if x > 0.0 then
    begin
      if x <> tf then
        ceil := Float(t + 1)
      else
        ceil := tf
    end
  else
    ceil := tf
end;
