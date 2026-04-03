program kpsc_routines;

var
  __CALL_RET: integer;

procedure ParseProcedureDecl;
begin
end;

function ParseFunctionDecl: integer;
begin
  ParseFunctionDecl := 0
end;

begin
  WriteLn(': MAIN');
  WriteLn('  9 PWRITE-I32');
  WriteLn('  PWRITELN');
  WriteLn(';');
  WriteLn('MAIN')
end.
