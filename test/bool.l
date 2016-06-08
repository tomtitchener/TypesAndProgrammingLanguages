# Church booleans
#
# Bindings
#
tru  = (λt.λf.t);
fls  = (λt.λf.f);
test = (λl.λm.λn. l m n);
#
and  = (λb.λc. b c fls);
or   = (λb.λc. b tru c);
not  = (λb. b fls tru);
l    = (λl.l);
m    = (λm.m);
#
# Statements
#
(test tru l m);
(test fls l m);
#
(and tru tru);
(and tru fls);
(and fls tru);
(and fls fls);
#
(or tru tru);
(or tru fls);
(or fls tru);
(or fls fls);
#
(not tru);
(not fls);
#
(not (not tru));
(not (not fls));
