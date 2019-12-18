(set-logic QF_LIA)
(declare-fun a_3 () Int)
(declare-fun a_2 () Int)
(declare-fun a_1 () Int)
(declare-fun a_0 () Int)
(declare-fun t_3 () Int)
(declare-fun t_2 () Int)
(declare-fun t_1 () Int)
(declare-fun t_0 () Int)
(declare-fun s_1 () Int)
(declare-fun x_0_4 () Int)
(declare-fun u_2_3 () Bool)
(declare-fun x_1_3 () Int)
(declare-fun u_1_3 () Bool)
(declare-fun s_0 () Int)
(declare-fun x_0_3 () Int)
(declare-fun u_0_3 () Bool)
(declare-fun u_2_4 () Bool)
(declare-fun u_1_4 () Bool)
(declare-fun u_0_4 () Bool)
(declare-fun x_2_3 () Int)
(declare-fun x_1_4 () Int)
(declare-fun x_2_4 () Int)
(declare-fun u_2_2 () Bool)
(declare-fun x_1_2 () Int)
(declare-fun u_1_2 () Bool)
(declare-fun x_0_2 () Int)
(declare-fun u_0_2 () Bool)
(declare-fun x_2_2 () Int)
(declare-fun u_2_1 () Bool)
(declare-fun x_1_1 () Int)
(declare-fun u_1_1 () Bool)
(declare-fun x_0_1 () Int)
(declare-fun u_0_1 () Bool)
(declare-fun x_2_1 () Int)
(declare-fun u_2_0 () Bool)
(declare-fun x_1_0 () Int)
(declare-fun u_1_0 () Bool)
(declare-fun x_0_0 () Int)
(declare-fun u_0_0 () Bool)
(declare-fun x_2_0 () Int)
(assert (let ((a!1 (and (= u_0_1 true) (= u_1_1 u_0_0) (= u_2_1 u_1_0)))
      (a!3 (and (= u_0_1 u_1_0) (= u_1_1 u_2_0) (= u_2_1 false)))
      (a!5 (and (= u_0_1 u_0_0) (= u_1_1 u_1_0) (= u_2_1 u_2_0)))
      (a!10 (and (= u_0_2 true) (= u_1_2 u_0_1) (= u_2_2 u_1_1)))
      (a!12 (and (= u_0_2 u_1_1) (= u_1_2 u_2_1) (= u_2_2 false)))
      (a!14 (and (= u_0_2 u_0_1) (= u_1_2 u_1_1) (= u_2_2 u_2_1)))
      (a!19 (and (= u_0_3 true) (= u_1_3 u_0_2) (= u_2_3 u_1_2)))
      (a!21 (and (= u_0_3 u_1_2) (= u_1_3 u_2_2) (= u_2_3 false)))
      (a!23 (and (= u_0_3 u_0_2) (= u_1_3 u_1_2) (= u_2_3 u_2_2)))
      (a!28 (and (= u_0_4 true) (= u_1_4 u_0_3) (= u_2_4 u_1_3)))
      (a!30 (and (= u_0_4 u_1_3) (= u_1_4 u_2_3) (= u_2_4 false)))
      (a!32 (and (= u_0_4 u_0_3) (= u_1_4 u_1_3) (= u_2_4 u_2_3))))
(let ((a!2 (and (= x_0_1 a_0)
                (=> u_1_1 (= x_1_1 x_0_0))
                (=> u_2_1 (= x_2_1 x_1_0))
                a!1))
      (a!4 (=> (= 32 t_0)
               (and u_0_0
                    (=> u_0_1 (= x_0_1 x_1_0))
                    (=> u_1_1 (= x_1_1 x_2_0))
                    a!3)))
      (a!6 (=> (= 33 t_0)
               (and u_0_0
                    u_1_0
                    (= x_0_1 x_1_0)
                    (= x_1_1 x_0_0)
                    (=> u_2_1 (= x_2_1 x_2_0))
                    a!5)))
      (a!7 (=> (= 34 t_0)
               (and a!1
                    (=> u_2_1 (= x_2_1 x_1_0))
                    a!1
                    u_0_0
                    (= x_0_0 x_0_0)
                    (not u_2_0)
                    (= x_0_1 x_0_0)
                    (not u_1_0)
                    (= x_1_1 x_0_0))))
      (a!8 (=> (= 35 t_0)
               (and (=> u_0_1 (= x_0_1 x_0_0))
                    (=> u_1_1 (= x_1_1 x_1_0))
                    (=> u_2_1 (= x_2_1 x_2_0))
                    a!5)))
      (a!9 (=> (= 36 t_0)
               (and a!3
                    (=> u_1_1 (= x_1_1 x_2_0))
                    a!3
                    u_0_0
                    (= x_0_0 s_0)
                    u_1_0
                    (= x_1_0 1)
                    (not u_2_0)
                    (= x_0_1 s_1))))
      (a!11 (and (= x_0_2 a_1)
                 (=> u_1_2 (= x_1_2 x_0_1))
                 (=> u_2_2 (= x_2_2 x_1_1))
                 a!10))
      (a!13 (=> (= 32 t_1)
                (and u_0_1
                     (=> u_0_2 (= x_0_2 x_1_1))
                     (=> u_1_2 (= x_1_2 x_2_1))
                     a!12)))
      (a!15 (=> (= 33 t_1)
                (and u_0_1
                     u_1_1
                     (= x_0_2 x_1_1)
                     (= x_1_2 x_0_1)
                     (=> u_2_2 (= x_2_2 x_2_1))
                     a!14)))
      (a!16 (=> (= 34 t_1)
                (and a!10
                     (=> u_2_2 (= x_2_2 x_1_1))
                     a!10
                     u_0_1
                     (= x_0_1 x_0_1)
                     (not u_2_1)
                     (= x_0_2 x_0_1)
                     (not u_1_1)
                     (= x_1_2 x_0_1))))
      (a!17 (=> (= 35 t_1)
                (and (=> u_0_2 (= x_0_2 x_0_1))
                     (=> u_1_2 (= x_1_2 x_1_1))
                     (=> u_2_2 (= x_2_2 x_2_1))
                     a!14)))
      (a!18 (=> (= 36 t_1)
                (and a!12
                     (=> u_1_2 (= x_1_2 x_2_1))
                     a!12
                     u_0_1
                     (= x_0_1 s_0)
                     u_1_1
                     (= x_1_1 1)
                     (not u_2_1)
                     (= x_0_2 s_1))))
      (a!20 (and (= x_0_3 a_2)
                 (=> u_1_3 (= x_1_3 x_0_2))
                 (=> u_2_3 (= x_2_3 x_1_2))
                 a!19))
      (a!22 (=> (= 32 t_2)
                (and u_0_2
                     (=> u_0_3 (= x_0_3 x_1_2))
                     (=> u_1_3 (= x_1_3 x_2_2))
                     a!21)))
      (a!24 (=> (= 33 t_2)
                (and u_0_2
                     u_1_2
                     (= x_0_3 x_1_2)
                     (= x_1_3 x_0_2)
                     (=> u_2_3 (= x_2_3 x_2_2))
                     a!23)))
      (a!25 (=> (= 34 t_2)
                (and a!19
                     (=> u_2_3 (= x_2_3 x_1_2))
                     a!19
                     u_0_2
                     (= x_0_2 x_0_2)
                     (not u_2_2)
                     (= x_0_3 x_0_2)
                     (not u_1_2)
                     (= x_1_3 x_0_2))))
      (a!26 (=> (= 35 t_2)
                (and (=> u_0_3 (= x_0_3 x_0_2))
                     (=> u_1_3 (= x_1_3 x_1_2))
                     (=> u_2_3 (= x_2_3 x_2_2))
                     a!23)))
      (a!27 (=> (= 36 t_2)
                (and a!21
                     (=> u_1_3 (= x_1_3 x_2_2))
                     a!21
                     u_0_2
                     (= x_0_2 s_0)
                     u_1_2
                     (= x_1_2 1)
                     (not u_2_2)
                     (= x_0_3 s_1))))
      (a!29 (and (= x_0_4 a_3)
                 (=> u_1_4 (= x_1_4 x_0_3))
                 (=> u_2_4 (= x_2_4 x_1_3))
                 a!28))
      (a!31 (=> (= 32 t_3)
                (and u_0_3
                     (=> u_0_4 (= x_0_4 x_1_3))
                     (=> u_1_4 (= x_1_4 x_2_3))
                     a!30)))
      (a!33 (=> (= 33 t_3)
                (and u_0_3
                     u_1_3
                     (= x_0_4 x_1_3)
                     (= x_1_4 x_0_3)
                     (=> u_2_4 (= x_2_4 x_2_3))
                     a!32)))
      (a!34 (=> (= 34 t_3)
                (and a!28
                     (=> u_2_4 (= x_2_4 x_1_3))
                     a!28
                     u_0_3
                     (= x_0_3 x_0_3)
                     (not u_2_3)
                     (= x_0_4 x_0_3)
                     (not u_1_3)
                     (= x_1_4 x_0_3))))
      (a!35 (=> (= 35 t_3)
                (and (=> u_0_4 (= x_0_4 x_0_3))
                     (=> u_1_4 (= x_1_4 x_1_3))
                     (=> u_2_4 (= x_2_4 x_2_3))
                     a!32)))
      (a!36 (=> (= 36 t_3)
                (and a!30
                     (=> u_1_4 (= x_1_4 x_2_3))
                     a!30
                     u_0_3
                     (= x_0_3 s_0)
                     u_1_3
                     (= x_1_3 1)
                     (not u_2_3)
                     (= x_0_4 s_1)))))
  (and (= x_0_0 s_0)
       (= u_0_0 true)
       (= u_1_0 false)
       (= u_2_0 false)
       (= x_0_4 146)
       (= u_0_4 true)
       (= x_1_4 s_1)
       (= u_1_4 true)
       (= u_2_4 false)
       (= s_0
          115792089237316195423570985008687907853269984665640564039457584007913129639936)
       (= s_1
          115792089237316195423570985008687907853269984665640564039457584007913129639937)
       (=> (= 0 t_0) (and (not u_2_0) (<= 1 a_0) (< a_0 256) a!2))
       (=> (= 1 t_0) (and (not u_2_0) (<= 256 a_0) (< a_0 65536) a!2))
       (=> (= 2 t_0) (and (not u_2_0) (<= 65536 a_0) (< a_0 16777216) a!2))
       (=> (= 3 t_0) (and (not u_2_0) (<= 16777216 a_0) (< a_0 4294967296) a!2))
       (=> (= 4 t_0)
           (and (not u_2_0) (<= 4294967296 a_0) (< a_0 1099511627776) a!2))
       (=> (= 5 t_0)
           (and (not u_2_0) (<= 1099511627776 a_0) (< a_0 281474976710656) a!2))
       (=> (= 6 t_0)
           (and (not u_2_0)
                (<= 281474976710656 a_0)
                (< a_0 72057594037927936)
                a!2))
       (=> (= 7 t_0)
           (and (not u_2_0)
                (<= 72057594037927936 a_0)
                (< a_0 18446744073709551616)
                a!2))
       (=> (= 8 t_0)
           (and (not u_2_0)
                (<= 18446744073709551616 a_0)
                (< a_0 4722366482869645213696)
                a!2))
       (=> (= 9 t_0)
           (and (not u_2_0)
                (<= 4722366482869645213696 a_0)
                (< a_0 1208925819614629174706176)
                a!2))
       (=> (= 10 t_0)
           (and (not u_2_0)
                (<= 1208925819614629174706176 a_0)
                (< a_0 309485009821345068724781056)
                a!2))
       (=> (= 11 t_0)
           (and (not u_2_0)
                (<= 309485009821345068724781056 a_0)
                (< a_0 79228162514264337593543950336)
                a!2))
       (=> (= 12 t_0)
           (and (not u_2_0)
                (<= 79228162514264337593543950336 a_0)
                (< a_0 20282409603651670423947251286016)
                a!2))
       (=> (= 13 t_0)
           (and (not u_2_0)
                (<= 20282409603651670423947251286016 a_0)
                (< a_0 5192296858534827628530496329220096)
                a!2))
       (=> (= 14 t_0)
           (and (not u_2_0)
                (<= 5192296858534827628530496329220096 a_0)
                (< a_0 1329227995784915872903807060280344576)
                a!2))
       (=> (= 15 t_0)
           (and (not u_2_0)
                (<= 1329227995784915872903807060280344576 a_0)
                (< a_0 340282366920938463463374607431768211456)
                a!2))
       (=> (= 16 t_0)
           (and (not u_2_0)
                (<= 340282366920938463463374607431768211456 a_0)
                (< a_0 87112285931760246646623899502532662132736)
                a!2))
       (=> (= 17 t_0)
           (and (not u_2_0)
                (<= 87112285931760246646623899502532662132736 a_0)
                (< a_0 22300745198530623141535718272648361505980416)
                a!2))
       (=> (= 18 t_0)
           (and (not u_2_0)
                (<= 22300745198530623141535718272648361505980416 a_0)
                (< a_0 5708990770823839524233143877797980545530986496)
                a!2))
       (=> (= 19 t_0)
           (and (not u_2_0)
                (<= 5708990770823839524233143877797980545530986496 a_0)
                (< a_0 1461501637330902918203684832716283019655932542976)
                a!2))
       (=> (= 20 t_0)
           (and (not u_2_0)
                (<= 1461501637330902918203684832716283019655932542976 a_0)
                (< a_0 374144419156711147060143317175368453031918731001856)
                a!2))
       (=> (= 21 t_0)
           (and (not u_2_0)
                (<= 374144419156711147060143317175368453031918731001856 a_0)
                (< a_0 95780971304118053647396689196894323976171195136475136)
                a!2))
       (=> (= 22 t_0)
           (and (not u_2_0)
                (<= 95780971304118053647396689196894323976171195136475136 a_0)
                (< a_0 24519928653854221733733552434404946937899825954937634816)
                a!2))
       (=> (= 23 t_0)
           (and (not u_2_0)
                (<= 24519928653854221733733552434404946937899825954937634816
                    a_0)
                (< a_0
                   6277101735386680763835789423207666416102355444464034512896)
                a!2))
       (=> (= 24 t_0)
           (and (not u_2_0)
                (<= 6277101735386680763835789423207666416102355444464034512896
                    a_0)
                (< a_0
                   1606938044258990275541962092341162602522202993782792835301376)
                a!2))
       (=> (= 25 t_0)
           (and (not u_2_0)
                (<= 1606938044258990275541962092341162602522202993782792835301376
                    a_0)
                (< a_0
                   411376139330301510538742295639337626245683966408394965837152256)
                a!2))
       (=> (= 26 t_0)
           (and (not u_2_0)
                (<= 411376139330301510538742295639337626245683966408394965837152256
                    a_0)
                (< a_0
                   105312291668557186697918027683670432318895095400549111254310977536)
                a!2))
       (=> (= 27 t_0)
           (and (not u_2_0)
                (<= 105312291668557186697918027683670432318895095400549111254310977536
                    a_0)
                (< a_0
                   26959946667150639794667015087019630673637144422540572481103610249216)
                a!2))
       (=> (= 28 t_0)
           (and (not u_2_0)
                (<= 26959946667150639794667015087019630673637144422540572481103610249216
                    a_0)
                (< a_0
                   6901746346790563787434755862277025452451108972170386555162524223799296)
                a!2))
       (=> (= 29 t_0)
           (and (not u_2_0)
                (<= 6901746346790563787434755862277025452451108972170386555162524223799296
                    a_0)
                (< a_0
                   1766847064778384329583297500742918515827483896875618958121606201292619776)
                a!2))
       (=> (= 30 t_0)
           (and (not u_2_0)
                (<= 1766847064778384329583297500742918515827483896875618958121606201292619776
                    a_0)
                (< a_0
                   452312848583266388373324160190187140051835877600158453279131187530910662656)
                a!2))
       (=> (= 31 t_0)
           (and (not u_2_0)
                (<= 452312848583266388373324160190187140051835877600158453279131187530910662656
                    a_0)
                (< a_0
                   115792089237316195423570985008687907853269984665640564039457584007913129639936)
                a!2))
       a!4
       a!6
       a!7
       a!8
       a!9
       (or (= 0 t_0)
           (= 1 t_0)
           (= 2 t_0)
           (= 3 t_0)
           (= 4 t_0)
           (= 5 t_0)
           (= 6 t_0)
           (= 7 t_0)
           (= 8 t_0)
           (= 9 t_0)
           (= 10 t_0)
           (= 11 t_0)
           (= 12 t_0)
           (= 13 t_0)
           (= 14 t_0)
           (= 15 t_0)
           (= 16 t_0)
           (= 17 t_0)
           (= 18 t_0)
           (= 19 t_0)
           (= 20 t_0)
           (= 21 t_0)
           (= 22 t_0)
           (= 23 t_0)
           (= 24 t_0)
           (= 25 t_0)
           (= 26 t_0)
           (= 27 t_0)
           (= 28 t_0)
           (= 29 t_0)
           (= 30 t_0)
           (= 31 t_0)
           (= 32 t_0)
           (= 33 t_0)
           (= 34 t_0)
           (= 35 t_0)
           (= 36 t_0))
       (=> (= 0 t_1) (and (not u_2_1) (<= 1 a_1) (< a_1 256) a!11))
       (=> (= 1 t_1) (and (not u_2_1) (<= 256 a_1) (< a_1 65536) a!11))
       (=> (= 2 t_1) (and (not u_2_1) (<= 65536 a_1) (< a_1 16777216) a!11))
       (=> (= 3 t_1)
           (and (not u_2_1) (<= 16777216 a_1) (< a_1 4294967296) a!11))
       (=> (= 4 t_1)
           (and (not u_2_1) (<= 4294967296 a_1) (< a_1 1099511627776) a!11))
       (=> (= 5 t_1)
           (and (not u_2_1) (<= 1099511627776 a_1) (< a_1 281474976710656) a!11))
       (=> (= 6 t_1)
           (and (not u_2_1)
                (<= 281474976710656 a_1)
                (< a_1 72057594037927936)
                a!11))
       (=> (= 7 t_1)
           (and (not u_2_1)
                (<= 72057594037927936 a_1)
                (< a_1 18446744073709551616)
                a!11))
       (=> (= 8 t_1)
           (and (not u_2_1)
                (<= 18446744073709551616 a_1)
                (< a_1 4722366482869645213696)
                a!11))
       (=> (= 9 t_1)
           (and (not u_2_1)
                (<= 4722366482869645213696 a_1)
                (< a_1 1208925819614629174706176)
                a!11))
       (=> (= 10 t_1)
           (and (not u_2_1)
                (<= 1208925819614629174706176 a_1)
                (< a_1 309485009821345068724781056)
                a!11))
       (=> (= 11 t_1)
           (and (not u_2_1)
                (<= 309485009821345068724781056 a_1)
                (< a_1 79228162514264337593543950336)
                a!11))
       (=> (= 12 t_1)
           (and (not u_2_1)
                (<= 79228162514264337593543950336 a_1)
                (< a_1 20282409603651670423947251286016)
                a!11))
       (=> (= 13 t_1)
           (and (not u_2_1)
                (<= 20282409603651670423947251286016 a_1)
                (< a_1 5192296858534827628530496329220096)
                a!11))
       (=> (= 14 t_1)
           (and (not u_2_1)
                (<= 5192296858534827628530496329220096 a_1)
                (< a_1 1329227995784915872903807060280344576)
                a!11))
       (=> (= 15 t_1)
           (and (not u_2_1)
                (<= 1329227995784915872903807060280344576 a_1)
                (< a_1 340282366920938463463374607431768211456)
                a!11))
       (=> (= 16 t_1)
           (and (not u_2_1)
                (<= 340282366920938463463374607431768211456 a_1)
                (< a_1 87112285931760246646623899502532662132736)
                a!11))
       (=> (= 17 t_1)
           (and (not u_2_1)
                (<= 87112285931760246646623899502532662132736 a_1)
                (< a_1 22300745198530623141535718272648361505980416)
                a!11))
       (=> (= 18 t_1)
           (and (not u_2_1)
                (<= 22300745198530623141535718272648361505980416 a_1)
                (< a_1 5708990770823839524233143877797980545530986496)
                a!11))
       (=> (= 19 t_1)
           (and (not u_2_1)
                (<= 5708990770823839524233143877797980545530986496 a_1)
                (< a_1 1461501637330902918203684832716283019655932542976)
                a!11))
       (=> (= 20 t_1)
           (and (not u_2_1)
                (<= 1461501637330902918203684832716283019655932542976 a_1)
                (< a_1 374144419156711147060143317175368453031918731001856)
                a!11))
       (=> (= 21 t_1)
           (and (not u_2_1)
                (<= 374144419156711147060143317175368453031918731001856 a_1)
                (< a_1 95780971304118053647396689196894323976171195136475136)
                a!11))
       (=> (= 22 t_1)
           (and (not u_2_1)
                (<= 95780971304118053647396689196894323976171195136475136 a_1)
                (< a_1 24519928653854221733733552434404946937899825954937634816)
                a!11))
       (=> (= 23 t_1)
           (and (not u_2_1)
                (<= 24519928653854221733733552434404946937899825954937634816
                    a_1)
                (< a_1
                   6277101735386680763835789423207666416102355444464034512896)
                a!11))
       (=> (= 24 t_1)
           (and (not u_2_1)
                (<= 6277101735386680763835789423207666416102355444464034512896
                    a_1)
                (< a_1
                   1606938044258990275541962092341162602522202993782792835301376)
                a!11))
       (=> (= 25 t_1)
           (and (not u_2_1)
                (<= 1606938044258990275541962092341162602522202993782792835301376
                    a_1)
                (< a_1
                   411376139330301510538742295639337626245683966408394965837152256)
                a!11))
       (=> (= 26 t_1)
           (and (not u_2_1)
                (<= 411376139330301510538742295639337626245683966408394965837152256
                    a_1)
                (< a_1
                   105312291668557186697918027683670432318895095400549111254310977536)
                a!11))
       (=> (= 27 t_1)
           (and (not u_2_1)
                (<= 105312291668557186697918027683670432318895095400549111254310977536
                    a_1)
                (< a_1
                   26959946667150639794667015087019630673637144422540572481103610249216)
                a!11))
       (=> (= 28 t_1)
           (and (not u_2_1)
                (<= 26959946667150639794667015087019630673637144422540572481103610249216
                    a_1)
                (< a_1
                   6901746346790563787434755862277025452451108972170386555162524223799296)
                a!11))
       (=> (= 29 t_1)
           (and (not u_2_1)
                (<= 6901746346790563787434755862277025452451108972170386555162524223799296
                    a_1)
                (< a_1
                   1766847064778384329583297500742918515827483896875618958121606201292619776)
                a!11))
       (=> (= 30 t_1)
           (and (not u_2_1)
                (<= 1766847064778384329583297500742918515827483896875618958121606201292619776
                    a_1)
                (< a_1
                   452312848583266388373324160190187140051835877600158453279131187530910662656)
                a!11))
       (=> (= 31 t_1)
           (and (not u_2_1)
                (<= 452312848583266388373324160190187140051835877600158453279131187530910662656
                    a_1)
                (< a_1
                   115792089237316195423570985008687907853269984665640564039457584007913129639936)
                a!11))
       a!13
       a!15
       a!16
       a!17
       a!18
       (or (= 0 t_1)
           (= 1 t_1)
           (= 2 t_1)
           (= 3 t_1)
           (= 4 t_1)
           (= 5 t_1)
           (= 6 t_1)
           (= 7 t_1)
           (= 8 t_1)
           (= 9 t_1)
           (= 10 t_1)
           (= 11 t_1)
           (= 12 t_1)
           (= 13 t_1)
           (= 14 t_1)
           (= 15 t_1)
           (= 16 t_1)
           (= 17 t_1)
           (= 18 t_1)
           (= 19 t_1)
           (= 20 t_1)
           (= 21 t_1)
           (= 22 t_1)
           (= 23 t_1)
           (= 24 t_1)
           (= 25 t_1)
           (= 26 t_1)
           (= 27 t_1)
           (= 28 t_1)
           (= 29 t_1)
           (= 30 t_1)
           (= 31 t_1)
           (= 32 t_1)
           (= 33 t_1)
           (= 34 t_1)
           (= 35 t_1)
           (= 36 t_1))
       (=> (= 0 t_2) (and (not u_2_2) (<= 1 a_2) (< a_2 256) a!20))
       (=> (= 1 t_2) (and (not u_2_2) (<= 256 a_2) (< a_2 65536) a!20))
       (=> (= 2 t_2) (and (not u_2_2) (<= 65536 a_2) (< a_2 16777216) a!20))
       (=> (= 3 t_2)
           (and (not u_2_2) (<= 16777216 a_2) (< a_2 4294967296) a!20))
       (=> (= 4 t_2)
           (and (not u_2_2) (<= 4294967296 a_2) (< a_2 1099511627776) a!20))
       (=> (= 5 t_2)
           (and (not u_2_2) (<= 1099511627776 a_2) (< a_2 281474976710656) a!20))
       (=> (= 6 t_2)
           (and (not u_2_2)
                (<= 281474976710656 a_2)
                (< a_2 72057594037927936)
                a!20))
       (=> (= 7 t_2)
           (and (not u_2_2)
                (<= 72057594037927936 a_2)
                (< a_2 18446744073709551616)
                a!20))
       (=> (= 8 t_2)
           (and (not u_2_2)
                (<= 18446744073709551616 a_2)
                (< a_2 4722366482869645213696)
                a!20))
       (=> (= 9 t_2)
           (and (not u_2_2)
                (<= 4722366482869645213696 a_2)
                (< a_2 1208925819614629174706176)
                a!20))
       (=> (= 10 t_2)
           (and (not u_2_2)
                (<= 1208925819614629174706176 a_2)
                (< a_2 309485009821345068724781056)
                a!20))
       (=> (= 11 t_2)
           (and (not u_2_2)
                (<= 309485009821345068724781056 a_2)
                (< a_2 79228162514264337593543950336)
                a!20))
       (=> (= 12 t_2)
           (and (not u_2_2)
                (<= 79228162514264337593543950336 a_2)
                (< a_2 20282409603651670423947251286016)
                a!20))
       (=> (= 13 t_2)
           (and (not u_2_2)
                (<= 20282409603651670423947251286016 a_2)
                (< a_2 5192296858534827628530496329220096)
                a!20))
       (=> (= 14 t_2)
           (and (not u_2_2)
                (<= 5192296858534827628530496329220096 a_2)
                (< a_2 1329227995784915872903807060280344576)
                a!20))
       (=> (= 15 t_2)
           (and (not u_2_2)
                (<= 1329227995784915872903807060280344576 a_2)
                (< a_2 340282366920938463463374607431768211456)
                a!20))
       (=> (= 16 t_2)
           (and (not u_2_2)
                (<= 340282366920938463463374607431768211456 a_2)
                (< a_2 87112285931760246646623899502532662132736)
                a!20))
       (=> (= 17 t_2)
           (and (not u_2_2)
                (<= 87112285931760246646623899502532662132736 a_2)
                (< a_2 22300745198530623141535718272648361505980416)
                a!20))
       (=> (= 18 t_2)
           (and (not u_2_2)
                (<= 22300745198530623141535718272648361505980416 a_2)
                (< a_2 5708990770823839524233143877797980545530986496)
                a!20))
       (=> (= 19 t_2)
           (and (not u_2_2)
                (<= 5708990770823839524233143877797980545530986496 a_2)
                (< a_2 1461501637330902918203684832716283019655932542976)
                a!20))
       (=> (= 20 t_2)
           (and (not u_2_2)
                (<= 1461501637330902918203684832716283019655932542976 a_2)
                (< a_2 374144419156711147060143317175368453031918731001856)
                a!20))
       (=> (= 21 t_2)
           (and (not u_2_2)
                (<= 374144419156711147060143317175368453031918731001856 a_2)
                (< a_2 95780971304118053647396689196894323976171195136475136)
                a!20))
       (=> (= 22 t_2)
           (and (not u_2_2)
                (<= 95780971304118053647396689196894323976171195136475136 a_2)
                (< a_2 24519928653854221733733552434404946937899825954937634816)
                a!20))
       (=> (= 23 t_2)
           (and (not u_2_2)
                (<= 24519928653854221733733552434404946937899825954937634816
                    a_2)
                (< a_2
                   6277101735386680763835789423207666416102355444464034512896)
                a!20))
       (=> (= 24 t_2)
           (and (not u_2_2)
                (<= 6277101735386680763835789423207666416102355444464034512896
                    a_2)
                (< a_2
                   1606938044258990275541962092341162602522202993782792835301376)
                a!20))
       (=> (= 25 t_2)
           (and (not u_2_2)
                (<= 1606938044258990275541962092341162602522202993782792835301376
                    a_2)
                (< a_2
                   411376139330301510538742295639337626245683966408394965837152256)
                a!20))
       (=> (= 26 t_2)
           (and (not u_2_2)
                (<= 411376139330301510538742295639337626245683966408394965837152256
                    a_2)
                (< a_2
                   105312291668557186697918027683670432318895095400549111254310977536)
                a!20))
       (=> (= 27 t_2)
           (and (not u_2_2)
                (<= 105312291668557186697918027683670432318895095400549111254310977536
                    a_2)
                (< a_2
                   26959946667150639794667015087019630673637144422540572481103610249216)
                a!20))
       (=> (= 28 t_2)
           (and (not u_2_2)
                (<= 26959946667150639794667015087019630673637144422540572481103610249216
                    a_2)
                (< a_2
                   6901746346790563787434755862277025452451108972170386555162524223799296)
                a!20))
       (=> (= 29 t_2)
           (and (not u_2_2)
                (<= 6901746346790563787434755862277025452451108972170386555162524223799296
                    a_2)
                (< a_2
                   1766847064778384329583297500742918515827483896875618958121606201292619776)
                a!20))
       (=> (= 30 t_2)
           (and (not u_2_2)
                (<= 1766847064778384329583297500742918515827483896875618958121606201292619776
                    a_2)
                (< a_2
                   452312848583266388373324160190187140051835877600158453279131187530910662656)
                a!20))
       (=> (= 31 t_2)
           (and (not u_2_2)
                (<= 452312848583266388373324160190187140051835877600158453279131187530910662656
                    a_2)
                (< a_2
                   115792089237316195423570985008687907853269984665640564039457584007913129639936)
                a!20))
       a!22
       a!24
       a!25
       a!26
       a!27
       (or (= 0 t_2)
           (= 1 t_2)
           (= 2 t_2)
           (= 3 t_2)
           (= 4 t_2)
           (= 5 t_2)
           (= 6 t_2)
           (= 7 t_2)
           (= 8 t_2)
           (= 9 t_2)
           (= 10 t_2)
           (= 11 t_2)
           (= 12 t_2)
           (= 13 t_2)
           (= 14 t_2)
           (= 15 t_2)
           (= 16 t_2)
           (= 17 t_2)
           (= 18 t_2)
           (= 19 t_2)
           (= 20 t_2)
           (= 21 t_2)
           (= 22 t_2)
           (= 23 t_2)
           (= 24 t_2)
           (= 25 t_2)
           (= 26 t_2)
           (= 27 t_2)
           (= 28 t_2)
           (= 29 t_2)
           (= 30 t_2)
           (= 31 t_2)
           (= 32 t_2)
           (= 33 t_2)
           (= 34 t_2)
           (= 35 t_2)
           (= 36 t_2))
       (=> (= 0 t_3) (and (not u_2_3) (<= 1 a_3) (< a_3 256) a!29))
       (=> (= 1 t_3) (and (not u_2_3) (<= 256 a_3) (< a_3 65536) a!29))
       (=> (= 2 t_3) (and (not u_2_3) (<= 65536 a_3) (< a_3 16777216) a!29))
       (=> (= 3 t_3)
           (and (not u_2_3) (<= 16777216 a_3) (< a_3 4294967296) a!29))
       (=> (= 4 t_3)
           (and (not u_2_3) (<= 4294967296 a_3) (< a_3 1099511627776) a!29))
       (=> (= 5 t_3)
           (and (not u_2_3) (<= 1099511627776 a_3) (< a_3 281474976710656) a!29))
       (=> (= 6 t_3)
           (and (not u_2_3)
                (<= 281474976710656 a_3)
                (< a_3 72057594037927936)
                a!29))
       (=> (= 7 t_3)
           (and (not u_2_3)
                (<= 72057594037927936 a_3)
                (< a_3 18446744073709551616)
                a!29))
       (=> (= 8 t_3)
           (and (not u_2_3)
                (<= 18446744073709551616 a_3)
                (< a_3 4722366482869645213696)
                a!29))
       (=> (= 9 t_3)
           (and (not u_2_3)
                (<= 4722366482869645213696 a_3)
                (< a_3 1208925819614629174706176)
                a!29))
       (=> (= 10 t_3)
           (and (not u_2_3)
                (<= 1208925819614629174706176 a_3)
                (< a_3 309485009821345068724781056)
                a!29))
       (=> (= 11 t_3)
           (and (not u_2_3)
                (<= 309485009821345068724781056 a_3)
                (< a_3 79228162514264337593543950336)
                a!29))
       (=> (= 12 t_3)
           (and (not u_2_3)
                (<= 79228162514264337593543950336 a_3)
                (< a_3 20282409603651670423947251286016)
                a!29))
       (=> (= 13 t_3)
           (and (not u_2_3)
                (<= 20282409603651670423947251286016 a_3)
                (< a_3 5192296858534827628530496329220096)
                a!29))
       (=> (= 14 t_3)
           (and (not u_2_3)
                (<= 5192296858534827628530496329220096 a_3)
                (< a_3 1329227995784915872903807060280344576)
                a!29))
       (=> (= 15 t_3)
           (and (not u_2_3)
                (<= 1329227995784915872903807060280344576 a_3)
                (< a_3 340282366920938463463374607431768211456)
                a!29))
       (=> (= 16 t_3)
           (and (not u_2_3)
                (<= 340282366920938463463374607431768211456 a_3)
                (< a_3 87112285931760246646623899502532662132736)
                a!29))
       (=> (= 17 t_3)
           (and (not u_2_3)
                (<= 87112285931760246646623899502532662132736 a_3)
                (< a_3 22300745198530623141535718272648361505980416)
                a!29))
       (=> (= 18 t_3)
           (and (not u_2_3)
                (<= 22300745198530623141535718272648361505980416 a_3)
                (< a_3 5708990770823839524233143877797980545530986496)
                a!29))
       (=> (= 19 t_3)
           (and (not u_2_3)
                (<= 5708990770823839524233143877797980545530986496 a_3)
                (< a_3 1461501637330902918203684832716283019655932542976)
                a!29))
       (=> (= 20 t_3)
           (and (not u_2_3)
                (<= 1461501637330902918203684832716283019655932542976 a_3)
                (< a_3 374144419156711147060143317175368453031918731001856)
                a!29))
       (=> (= 21 t_3)
           (and (not u_2_3)
                (<= 374144419156711147060143317175368453031918731001856 a_3)
                (< a_3 95780971304118053647396689196894323976171195136475136)
                a!29))
       (=> (= 22 t_3)
           (and (not u_2_3)
                (<= 95780971304118053647396689196894323976171195136475136 a_3)
                (< a_3 24519928653854221733733552434404946937899825954937634816)
                a!29))
       (=> (= 23 t_3)
           (and (not u_2_3)
                (<= 24519928653854221733733552434404946937899825954937634816
                    a_3)
                (< a_3
                   6277101735386680763835789423207666416102355444464034512896)
                a!29))
       (=> (= 24 t_3)
           (and (not u_2_3)
                (<= 6277101735386680763835789423207666416102355444464034512896
                    a_3)
                (< a_3
                   1606938044258990275541962092341162602522202993782792835301376)
                a!29))
       (=> (= 25 t_3)
           (and (not u_2_3)
                (<= 1606938044258990275541962092341162602522202993782792835301376
                    a_3)
                (< a_3
                   411376139330301510538742295639337626245683966408394965837152256)
                a!29))
       (=> (= 26 t_3)
           (and (not u_2_3)
                (<= 411376139330301510538742295639337626245683966408394965837152256
                    a_3)
                (< a_3
                   105312291668557186697918027683670432318895095400549111254310977536)
                a!29))
       (=> (= 27 t_3)
           (and (not u_2_3)
                (<= 105312291668557186697918027683670432318895095400549111254310977536
                    a_3)
                (< a_3
                   26959946667150639794667015087019630673637144422540572481103610249216)
                a!29))
       (=> (= 28 t_3)
           (and (not u_2_3)
                (<= 26959946667150639794667015087019630673637144422540572481103610249216
                    a_3)
                (< a_3
                   6901746346790563787434755862277025452451108972170386555162524223799296)
                a!29))
       (=> (= 29 t_3)
           (and (not u_2_3)
                (<= 6901746346790563787434755862277025452451108972170386555162524223799296
                    a_3)
                (< a_3
                   1766847064778384329583297500742918515827483896875618958121606201292619776)
                a!29))
       (=> (= 30 t_3)
           (and (not u_2_3)
                (<= 1766847064778384329583297500742918515827483896875618958121606201292619776
                    a_3)
                (< a_3
                   452312848583266388373324160190187140051835877600158453279131187530910662656)
                a!29))
       (=> (= 31 t_3)
           (and (not u_2_3)
                (<= 452312848583266388373324160190187140051835877600158453279131187530910662656
                    a_3)
                (< a_3
                   115792089237316195423570985008687907853269984665640564039457584007913129639936)
                a!29))
       a!31
       a!33
       a!34
       a!35
       a!36
       (or (= 0 t_3)
           (= 1 t_3)
           (= 2 t_3)
           (= 3 t_3)
           (= 4 t_3)
           (= 5 t_3)
           (= 6 t_3)
           (= 7 t_3)
           (= 8 t_3)
           (= 9 t_3)
           (= 10 t_3)
           (= 11 t_3)
           (= 12 t_3)
           (= 13 t_3)
           (= 14 t_3)
           (= 15 t_3)
           (= 16 t_3)
           (= 17 t_3)
           (= 18 t_3)
           (= 19 t_3)
           (= 20 t_3)
           (= 21 t_3)
           (= 22 t_3)
           (= 23 t_3)
           (= 24 t_3)
           (= 25 t_3)
           (= 26 t_3)
           (= 27 t_3)
           (= 28 t_3)
           (= 29 t_3)
           (= 30 t_3)
           (= 31 t_3)
           (= 32 t_3)
           (= 33 t_3)
           (= 34 t_3)
           (= 35 t_3)
           (= 36 t_3))
       (=> (= t_0 35) (= t_1 35))
       (=> (= t_1 35) (= t_2 35))
       (=> (= t_2 35) (= t_3 35))
       (<= 0 a_0)
       (< a_0
          115792089237316195423570985008687907853269984665640564039457584007913129639936)
       (<= 0 a_1)
       (< a_1
          115792089237316195423570985008687907853269984665640564039457584007913129639936)
       (<= 0 a_2)
       (< a_2
          115792089237316195423570985008687907853269984665640564039457584007913129639936)
       (<= 0 a_3)
       (< a_3
          115792089237316195423570985008687907853269984665640564039457584007913129639936)))))
(assert-soft (! (or (= 35 t_0) (= 32 t_0)) :weight 1 :id gas))
(assert-soft (! (= 35 t_0) :weight 2 :id gas))
(assert-soft (! (or (= 35 t_1) (= 32 t_1)) :weight 1 :id gas))
(assert-soft (! (= 35 t_1) :weight 2 :id gas))
(assert-soft (! (or (= 35 t_2) (= 32 t_2)) :weight 1 :id gas))
(assert-soft (! (= 35 t_2) :weight 2 :id gas))
(assert-soft (! (or (= 35 t_3) (= 32 t_3)) :weight 1 :id gas))
(assert-soft (! (= 35 t_3) :weight 2 :id gas))
(check-sat)
(get-model)
