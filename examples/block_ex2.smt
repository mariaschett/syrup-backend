; 
(set-info :status unknown)
(declare-fun a_2 () Int)
(declare-fun a_1 () Int)
(declare-fun a_0 () Int)
(declare-fun t_2 () Int)
(declare-fun t_1 () Int)
(declare-fun t_0 () Int)
(declare-fun x_2_2 () Int)
(declare-fun x_2_3 () Int)
(declare-fun x_1_2 () Int)
(declare-fun x_1_3 () Int)
(declare-fun x_0_2 () Int)
(declare-fun x_0_3 () Int)
(declare-fun x_2_1 () Int)
(declare-fun x_1_1 () Int)
(declare-fun x_0_1 () Int)
(declare-fun x_2_0 () Int)
(declare-fun x_1_0 () Int)
(declare-fun x_0_0 () Int)
(declare-fun sk_x () Int)
(declare-fun u_2_2 () Bool)
(declare-fun u_2_3 () Bool)
(declare-fun u_1_2 () Bool)
(declare-fun u_1_3 () Bool)
(declare-fun u_0_2 () Bool)
(declare-fun u_0_3 () Bool)
(declare-fun u_2_1 () Bool)
(declare-fun u_1_1 () Bool)
(declare-fun u_0_1 () Bool)
(declare-fun u_2_0 () Bool)
(declare-fun u_1_0 () Bool)
(declare-fun u_0_0 () Bool)
(assert
 (let (($x403 (and (and (<= 0 a_0) (< a_0 1024)) (and (<= 0 a_1) (< a_1 1024)) (and (<= 0 a_2) (< a_2 1024)))))
 (let (($x404 (and (=> (= t_0 4) (= t_1 4)) (=> (= t_1 4) (= t_2 4)))))
 (let (($x391 (= 4 t_2)))
 (let (($x208 (= 3 t_2)))
 (let (($x207 (= 2 t_2)))
 (let (($x206 (= 1 t_2)))
 (let (($x205 (= 0 t_2)))
 (let (($x215 (= u_2_3 u_2_2)))
 (let (($x212 (= u_1_3 u_1_2)))
 (let (($x209 (= u_0_3 u_0_2)))
 (let (($x214 (and $x209 $x212 $x215)))
 (let (($x216 (= x_2_3 x_2_2)))
 (let (($x211 (=> u_2_3 $x216)))
 (let (($x245 (and (=> u_0_3 (= x_0_3 x_0_2)) (=> u_1_3 (= x_1_3 x_1_2)) $x211)))
 (let (($x393 (= u_2_3 u_1_2)))
 (let (($x385 (= u_1_3 u_0_2)))
 (let (($x241 (= u_0_3 true)))
 (let (($x386 (and $x241 $x385 $x393)))
 (let (($x397 (= x_2_3 x_1_2)))
 (let (($x306 (=> u_2_3 $x397)))
 (let (($x394 (= x_1_3 x_0_2)))
 (let (($x235 (= x_0_3 x_0_2)))
 (let (($x373 (not u_2_2)))
 (let (($x237 (=> $x208 (and u_0_2 (and $x373 (and $x235 (and $x394 (and $x306 $x386))))))))
 (let (($x220 (and u_0_2 (and u_1_2 (and (and (= x_0_3 x_1_2) $x394) (and $x211 $x214))))))
 (let (($x171 (and (=> u_0_3 (= x_0_3 x_1_2)) (=> u_1_3 (= x_1_3 x_2_2)))))
 (let (($x213 (and $x171 (and (= u_0_3 u_1_2) (= u_1_3 u_2_2) (= u_2_3 false)))))
 (let (($x375 (and $x373 (and (= x_0_3 a_2) (and (and (=> u_1_3 $x394) $x306) $x386)))))
 (let (($x255 (and (=> $x205 $x375) (=> $x206 (and u_0_2 $x213)) (=> $x207 $x220) $x237 (=> $x391 (and $x245 $x214)))))
 (let (($x146 (= 4 t_1)))
 (let (($x145 (= 3 t_1)))
 (let (($x188 (and (= u_0_2 u_0_1) (= u_1_2 u_1_1) (= u_2_2 u_2_1))))
 (let (($x186 (=> u_2_2 (= x_2_2 x_2_1))))
 (let (($x201 (and (=> u_0_2 (= x_0_2 x_0_1)) (=> u_1_2 (= x_1_2 x_1_1)) $x186)))
 (let (($x165 (and (= u_0_2 true) (= u_1_2 u_0_1) (= u_2_2 u_1_1))))
 (let (($x155 (=> u_2_2 (= x_2_2 x_1_1))))
 (let (($x167 (= x_1_2 x_0_1)))
 (let (($x382 (= x_0_2 x_0_1)))
 (let (($x173 (not u_2_1)))
 (let (($x198 (=> $x145 (and u_0_1 (and $x173 (and $x382 (and $x167 (and $x155 $x165))))))))
 (let (($x196 (and u_0_1 (and u_1_1 (and (and (= x_0_2 x_1_1) $x167) (and $x186 $x188))))))
 (let (($x183 (and (=> u_0_2 (= x_0_2 x_1_1)) (=> u_1_2 (= x_1_2 x_2_1)))))
 (let (($x184 (and $x183 (and (= u_0_2 u_1_1) (= u_1_2 u_2_1) (= u_2_2 false)))))
 (let (($x147 (and $x173 (and (= x_0_2 a_1) (and (and (=> u_1_2 $x167) $x155) $x165)))))
 (let (($x204 (and (=> (= 0 t_1) $x147) (=> (= 1 t_1) (and u_0_1 $x184)) (=> (= 2 t_1) $x196) $x198 (=> $x146 (and $x201 $x188)))))
 (let (($x150 (and $x204 (or (= 0 t_1) (= 1 t_1) (= 2 t_1) $x145 $x146))))
 (let (($x71 (= 4 t_0)))
 (let (($x70 (= 3 t_0)))
 (let (($x68 (= 2 t_0)))
 (let (($x66 (= 1 t_0)))
 (let (($x65 (= 0 t_0)))
 (let (($x132 (and (=> u_0_1 (= x_0_1 x_0_0)) (=> u_1_1 (= x_1_1 x_1_0)) (=> u_2_1 (= x_2_1 x_2_0)))))
 (let (($x133 (and $x132 (and (= u_0_1 u_0_0) (= u_1_1 u_1_0) (= u_2_1 u_2_0)))))
 (let (($x122 (and (=> u_2_1 (= x_2_1 x_1_0)) (and (= u_0_1 true) (= u_1_1 u_0_0) (= u_2_1 u_1_0)))))
 (let (($x84 (= x_1_1 x_0_0)))
 (let (($x127 (and u_0_0 (and (not u_2_0) (and (= x_0_1 x_0_0) (and $x84 $x122))))))
 (let (($x116 (and (=> u_2_1 (= x_2_1 x_2_0)) (and (= u_0_1 u_0_0) (= u_1_1 u_1_0) (= u_2_1 u_2_0)))))
 (let (($x121 (=> $x68 (and u_0_0 (and u_1_0 (and (and (= x_0_1 x_1_0) $x84) $x116))))))
 (let (($x106 (and (=> u_0_1 (= x_0_1 x_1_0)) (=> u_1_1 (= x_1_1 x_2_0)))))
 (let (($x107 (and $x106 (and (= u_0_1 u_1_0) (= u_1_1 u_2_0) (= u_2_1 false)))))
 (let (($x91 (and (and (=> u_1_1 $x84) (=> u_2_1 (= x_2_1 x_1_0))) (and (= u_0_1 true) (= u_1_1 u_0_0) (= u_2_1 u_1_0)))))
 (let (($x388 (and (=> $x65 (and (not u_2_0) (and (= x_0_1 a_0) $x91))) (=> $x66 (and u_0_0 $x107)) $x121 (=> $x70 $x127) (=> $x71 $x133))))
 (let (($x253 (and (and $x388 (or $x65 $x66 $x68 $x70 $x71)) $x150 (and $x255 (or $x205 $x206 $x207 $x208 $x391)))))
 (let (($x256 (= u_2_3 false)))
 (let (($x402 (and (and (= x_0_3 sk_x) $x241) (and (= x_1_3 sk_x) (= u_1_3 true)) $x256)))
 (let (($x18 (and (and (= x_0_0 sk_x) (= u_0_0 true)) (= u_1_0 false) (= u_2_0 false))))
 (and $x18 (and $x402 (and (= sk_x 1024) (and $x253 (and $x404 $x403))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
(get-model)