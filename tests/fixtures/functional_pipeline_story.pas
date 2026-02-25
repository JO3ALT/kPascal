program functionalpipelinestory;
type
  status = (cold, warm, hot);
  config = record
    offset: integer;
    threshold: integer;
  end;
  i8 = array[-3..4] of integer;
  rint = result of integer, integer;
var
  cfg: config;
  i: integer;
  raw: i8;
  shifted: i8;
  patched: i8;
  hot_only: i8;
  n: integer;
  total: integer;
  avg: integer;
  avg_res: rint;
  st: status;

function classify(v: integer): status;
begin
  classify := cond(
    v < 10: begin
      value cold
    end;
    v < 20: begin
      value warm
    end;
    else: begin
      value hot
    end
  )
end;

begin
  cfg := config(offset := 3; threshold := 15);
  raw := [2, 7, 11, 13, 17, 19, 23, 29];

  WriteLn(Low(raw));
  WriteLn(High(raw));
  WriteLn(raw[-3]);
  WriteLn(raw[4]);

  for i := 0 to 7 do
    shifted[i - 3] := raw[i - 3] + cfg.offset;
  WriteArr(shifted, 8);

  patched := shifted with [-3 := 99, 4 := 77];
  WriteLn(patched[-3]);
  WriteLn(patched[4]);

  cfg := cfg with (threshold := 18);
  n := 0;
  for i := -3 to 4 do
    if shifted[i] >= cfg.threshold then
    begin
      hot_only[n + Low(hot_only)] := shifted[i];
      n := n + 1
    end;
  WriteLn(n);
  WriteArr(hot_only, n);

  total := 0;
  for i := 0 to n - 1 do
    total := total + hot_only[i + Low(hot_only)];
  WriteLn(total);

  avg_res := cond(
    n > 0: begin
      value ok(value := total div n)
    end;
    else: begin
      value err(error := -1)
    end
  );

  case avg_res of
    ok(v): begin
      avg := v;
      WriteLn(v)
    end;
    err(e): begin
      avg := 0;
      WriteLn(e)
    end
  end;

  st := classify(avg);
  case st of
    cold: WriteLn(100);
    warm: WriteLn(200);
    hot: WriteLn(300)
  end
end.
