program extensionsshowcaseannotated;
const
  answer: integer = 42;
  flag_true: boolean = true;
  bang: char = '!';
type
  color = (red, green, blue);
  shape = (circle, square);
  optint = option of integer;
  pair = record
    x: integer;
    y: integer;
  end;
  s8 = array[8] of char;
var
  c: color;
  picked: optint;
  tmp_pair: pair;
  tmp_str: s8;
  score: integer;

imut
  fixed_pair: pair;
  title: s8;

function PickPositive(a: integer; b: integer): optint;
begin
  PickPositive := cond(
    a > 0: begin
      value some(a)
    end;
    b > 0: begin
      value some(b)
    end;
    else: begin
      value none
    end
  )
end;

begin
  tmp_pair.x := 7;
  tmp_pair.y := 8;
  fixed_pair := tmp_pair;   { OK: imut 初期化（1回のみ） }

  tmp_str := 'EXT';
  title := tmp_str;         { OK: imut 初期化（1回のみ） }

  c := green;
  picked := PickPositive(-3, answer);

  WriteLn(answer);
  WriteLn(flag_true);
  WriteLn(bang);
  WriteLn(Ord(c));          { enum を序数化 }

  case c of
    red: WriteLn('RED');
    green: WriteLn('GREEN');
    blue: WriteLn('BLUE')
  end;

  score := cond(
    c = green: begin
      value 100
    end;
    else: begin
      value 0
    end
  );
  WriteLn(score);

  case picked of
    none(): WriteLn(0);
    some(v): WriteLn(v)
  end;

  WriteLn(fixed_pair.x + fixed_pair.y);
  WriteLn(title);

  { ---- 以下は意図的なエラー例（コメントアウト） ---- }
  { c := 1; }              { NG: enum color と integer は別型 }
  { c := circle; }         { NG: enum color と enum shape は別型 }
  { title := 'AGAIN'; }    { NG: imut 再代入 }
  { fixed_pair.x := 9; }   { NG: imut の field 更新 }
end.
