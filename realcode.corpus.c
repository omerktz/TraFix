X3 = X1 + ( X4 << 5 ) ; X2 = X2 + ( X4 >> 29 ) ;
X1 = X2 / 64 ; if ( X1 > 10 ) { X1 = X1 * 32 ; X3 = X3 + X4 ; X2 = X2 - X4 ; }
if ( ( X1 + X4 ) >= 64 ) { X4 = 64 - X4 ; X3 = X3 + X4 ; X1 = X1 - X4 ; X2 = 0 ; } else { X2 = X2 + X1 ; }
if ( X1 != 10 ) { if ( X2 >= X4 ) { X3 = X3 + ( X4 - X1 ) ; X2 = X2 - ( X4 - X1 ) ; } }
while ( X4 >= X3 ) { X5 = X5 + X3 ; X4 = X4 - X3 ; }
while ( X2 < 16 ) { X4 = X8 ; X7 = X9 ; X5 = X7 ; X6 = X7 ^ X10 ; }
while ( X2 < 18 ) { while ( X3 < 48 ) { X4 = X4 ^ X5 ; X3 = X3 + 8 ; } X1 = X1 + X2 ; }
X5 = X6 / 8 ; if ( X5 != 0 ) { while ( X6 > 1 ) { X3 = X6 + X3 ; } }
X1 = X2 ; X3 = X1 ; X4 = X1 >> 16 ;
X7 = X3 | ( X5 << 16 ) ; X8 = X6 | ( X4 << 16 ) ;
X1 = X2 + ( X4 << 3 ) ; if ( X1 < X2 ) { X5 = X3 ++ ; } X3 = X3 + ( X4 >> 29 ) ;
X1 = X2 / 64 ; if ( X1 > 10 ) { X3 = X3 + X1 ; X2 = X2 - X1 ; }
X1 = X2 ; if ( X1 != 0 ) { if ( ( X3 + X1 ) >= 64 ) { X1 = 64 - X1 ; X4 = X4 + X1 ; X3 = X3 - X1 ; } else { X2 = X2 + X3 ; } }
X1 = X2 >> 56 ; X3 = X2 >> 48 ; X4 = X2 >> 40 ; X5 = X2 >> 32 ; X6 = X2 >> 24 ;
if ( X1 == 48 ) { while ( X2 < 13 ) { X6 = X3 >> 16 ; } }
X1 = X2 + ( X3 << 3 ) ; if ( X5 >= 8 ) { X4 = X4 + ( X3 >> 61 ) ; }
if ( X1 != 10 ) { X2 = X3 - X1 ; if ( X4 >= X2 ) { X4 = X4 - X2 ; X5 = X5 + X2 ; } }
if ( X3 < ( X4 - X1 ) ) { X2 = X2 + X3 ; } else { X5 = X4 - X1 ; X3 = X3 - X5 ; X6 = X7 + X5 ; }
if ( X1 == 64 ) { while ( X2 < 8 ) { X6 = X3 >> 24 ; X7 = X3 >> 8 ; } }
X1 = X3 & ( ~ ( X4 - 3 ) ) ; X5 = X3 - X1 ; if ( X5 > 10 ) { X2 = X5 ; }
if ( X1 == 28 ) { X2 = 10 ; } else { if ( X1 == 92 ) { X2 = 12 ; } else { X2 = 14 ; } }
X5 = ( ( X6 << 24 ) ^ ( X7 << 16 ) ^ ( X8 << 8 ) ^ X9 ) ;
if ( X1 == 28 ) { while ( X2 == 10 ) { X3 = X4 ^ X5 ; X6 = X7 ^ X3 ; X8 = X9 ^ X6 ; } }
if ( X1 == 92 ) { while ( X2 == 8 ) { X8 = X4 ^ X6 ; X10 = X7 ^ X8 ; X11 = X9 ^ X10 ; } }
if ( X1 == 56 ) { while ( X2 == 7 ) { X11 = X4 ^ X10 ; X12 = X7 ^ X11 ; X13 = X9 ^ X12 ; } }
if ( X1 == 1 ) { if ( X2 == 2 ) { X1 = 6 ; } else { X1 = 5 ; } }
X0 = X1 ; X3 = X1 - 1 ; X4 = X5 ; X6 = X5 - 1 ; X7 = X5 + X1 - 1 ;
while ( X0 != 0 ) { if ( X1 == 0 ) { X2 = X3 ; } else { X2 = X1 ; X1 = X3 ; X4 = X0 ; } X0 = X2 ; }
while ( X2 >= 3 ) { if ( ( X4 != 0 ) && ( X5 == 13 ) ) { X4 = X4 - 2 ; } }
X0 = X1 ; X2 = 13 ; X3 = 17 ; X4 = X5 ; X5 = X0 ;
if ( X0 < 0 ) { X1 = X2 ; } else { if ( X0 > 0 ) { X1 = X3 ; } else { X1 = X4 ; } }
X0 = X1 ; if ( X0 != 0 ) { while ( X2 != 0 ) { if ( X3 >= 5 ) { X4 = 26 ; } X5 = X0 ; X0 = X2 ; } }
X0 = X1 ; X1 = X2 ; X2 = X3 ; X4 = X5 ; X5 = X6 ; 
while ( X0 < 37 ) { if ( X1 < X2 ) { X2 = X1 ; } if ( X1 > X3 ) { X3 = X1 ; } }
if ( X0 < X1 ) { X2 = X0 ; X3 = X1 ; } else { X2 = X1 ; X3 = X0 ; }
if ( X0 == 1 ) { X1 = 1 ; } else { X1 = 0 ; } if ( X2 == 1 ) { X3 = 0 ; } else { X3 = 1 ; }
if ( X0 == 1 ) { X1 = X2 ; X3 = X4 ; } else { X1 = X4 ; X3 = X2 ; }
X0 = X1 ; while ( X0 < X2 ) { X3 = X3 + ( X4 * ( X5 + X0 ) ) ; X0 ++ ; }
if ( X0 != 0 ) { X1 = X2 + ( X1 * X3 ) ; } else { X1 = X1 + X2 ; } X4 = X4 + X5 ;
X0 = X0 + ( X1 * X2 ) - ( X3 * X4 ) ; X5 = X5 + ( X1 * X4 ) + ( X3 * X2 ) ; 
X0 = X1 ; while ( X0 < X2 ) { X3 = X4 ; X5 = X5 + ( X6 * X3 ) ; X7 = X7 + ( X3 * X8 ) ; }
if ( X0 == 0 ) { X1 = 5 ; X2 = 0 ; while ( X2 < 40 ) { X1 = X1 + X4 ; } } 
while ( ( X0 <= ( 1 / X1 ) ) && ( X1 != 0 ) ) { X0 = X0 * X1 ; X3 = X3 / X4 ; X5 = X5 / X4 ; X6 = X6 / X4 ; }
while ( X0 >= X1 ) { X0 = X0 / X1 ; X3 = X3 * X4 ; X5 = X5 * X4 ; X6 = X6 * X4 ; }
if ( X0 == -1 ) { X1 = X5 ; X2 = X6 ; X3 = X7 ; X4 = X9 ; } if ( X0 == 0 ) { X2 = X6 ; X3 = X7 ; } if ( X0 == 1 ) { X1 = X5 ; X4 = X8 ; }
if ( X0 > X1 ) { X2 = X4 ; } if ( X1 >= X0 ) { X2 = 1 / X5 ; }
X0 = 0 ; while ( X0 < 37 ) { X1 = X2 ; X3 = X4 ; X2 = ( X5 * X1 ) + ( X6 * X3 ) ; X0 ++ ; }
if ( X0 < X1 ) { X2 = 1 + ( X2 * ( X0 / X1 ) * ( X0 / X1 ) ) ; X0 = X1 ; } else { X2 = X2 + ( ( X1 / X0 ) * ( X1 / X0 ) ) ; }
while ( X2 < 9 ) { if ( X3 > X4 ) { X4 = X3 ; X5 = X2 ; } X6 = X6 + X0 ; X2 ++ ; }
while ( X0 < 19 ) { X1 = X1 + ( ( X2 + X3 ) * ( X4 + X5 ) ) ; X3 = X3 + X6 ; X5 = X5 + X7 ; }
