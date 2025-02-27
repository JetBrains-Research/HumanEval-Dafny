method Main()
  decreases *
{
	{var v := add(0, 1); expect v == 1, "test 0 failed";}
	{var v := add(1, 0); expect v == 1, "test 1 failed";}
	{var v := add(2, 3); expect v == 5, "test 2 failed";}
	{var v := add(5, 7); expect v == 12, "test 3 failed";}
	{var v := add(7, 5); expect v == 12, "test 4 failed";}
	{var v := add(480, 593); expect v == 1073, "test 5 failed";}
	{var v := add(139, 579); expect v == 718, "test 6 failed";}
	{var v := add(300, 77); expect v == 377, "test 7 failed";}
	{var v := add(569, 756); expect v == 1325, "test 8 failed";}
	{var v := add(911, 703); expect v == 1614, "test 9 failed";}
	{var v := add(197, 326); expect v == 523, "test 10 failed";}
	{var v := add(123, 102); expect v == 225, "test 11 failed";}
	{var v := add(671, 705); expect v == 1376, "test 12 failed";}
	{var v := add(101, 721); expect v == 822, "test 13 failed";}
	{var v := add(735, 413); expect v == 1148, "test 14 failed";}
	{var v := add(923, 369); expect v == 1292, "test 15 failed";}
	{var v := add(938, 221); expect v == 1159, "test 16 failed";}
	{var v := add(59, 772); expect v == 831, "test 17 failed";}
	{var v := add(540, 790); expect v == 1330, "test 18 failed";}
	{var v := add(244, 6); expect v == 250, "test 19 failed";}
	{var v := add(705, 148); expect v == 853, "test 20 failed";}
	{var v := add(890, 180); expect v == 1070, "test 21 failed";}
	{var v := add(342, 129); expect v == 471, "test 22 failed";}
	{var v := add(946, 559); expect v == 1505, "test 23 failed";}
	{var v := add(623, 593); expect v == 1216, "test 24 failed";}
	{var v := add(825, 294); expect v == 1119, "test 25 failed";}
	{var v := add(124, 732); expect v == 856, "test 26 failed";}
	{var v := add(333, 987); expect v == 1320, "test 27 failed";}
	{var v := add(269, 347); expect v == 616, "test 28 failed";}
	{var v := add(826, 822); expect v == 1648, "test 29 failed";}
	{var v := add(157, 479); expect v == 636, "test 30 failed";}
	{var v := add(534, 184); expect v == 718, "test 31 failed";}
	{var v := add(418, 549); expect v == 967, "test 32 failed";}
	{var v := add(855, 765); expect v == 1620, "test 33 failed";}
	{var v := add(666, 55); expect v == 721, "test 34 failed";}
	{var v := add(428, 315); expect v == 743, "test 35 failed";}
	{var v := add(704, 645); expect v == 1349, "test 36 failed";}
	{var v := add(183, 272); expect v == 455, "test 37 failed";}
	{var v := add(966, 528); expect v == 1494, "test 38 failed";}
	{var v := add(571, 697); expect v == 1268, "test 39 failed";}
	{var v := add(610, 541); expect v == 1151, "test 40 failed";}
	{var v := add(249, 665); expect v == 914, "test 41 failed";}
	{var v := add(452, 186); expect v == 638, "test 42 failed";}
	{var v := add(421, 529); expect v == 950, "test 43 failed";}
	{var v := add(860, 376); expect v == 1236, "test 44 failed";}
	{var v := add(172, 601); expect v == 773, "test 45 failed";}
	{var v := add(30, 177); expect v == 207, "test 46 failed";}
	{var v := add(35, 753); expect v == 788, "test 47 failed";}
	{var v := add(818, 902); expect v == 1720, "test 48 failed";}
	{var v := add(618, 175); expect v == 793, "test 49 failed";}
	{var v := add(165, 302); expect v == 467, "test 50 failed";}
	{var v := add(405, 836); expect v == 1241, "test 51 failed";}
	{var v := add(574, 555); expect v == 1129, "test 52 failed";}
	{var v := add(152, 343); expect v == 495, "test 53 failed";}
	{var v := add(882, 225); expect v == 1107, "test 54 failed";}
	{var v := add(670, 359); expect v == 1029, "test 55 failed";}
	{var v := add(480, 476); expect v == 956, "test 56 failed";}
	{var v := add(265, 822); expect v == 1087, "test 57 failed";}
	{var v := add(390, 904); expect v == 1294, "test 58 failed";}
	{var v := add(570, 503); expect v == 1073, "test 59 failed";}
	{var v := add(660, 18); expect v == 678, "test 60 failed";}
	{var v := add(457, 319); expect v == 776, "test 61 failed";}
	{var v := add(724, 18); expect v == 742, "test 62 failed";}
	{var v := add(469, 235); expect v == 704, "test 63 failed";}
	{var v := add(91, 322); expect v == 413, "test 64 failed";}
	{var v := add(91, 789); expect v == 880, "test 65 failed";}
	{var v := add(361, 945); expect v == 1306, "test 66 failed";}
	{var v := add(272, 952); expect v == 1224, "test 67 failed";}
	{var v := add(567, 768); expect v == 1335, "test 68 failed";}
	{var v := add(264, 478); expect v == 742, "test 69 failed";}
	{var v := add(57, 615); expect v == 672, "test 70 failed";}
	{var v := add(301, 553); expect v == 854, "test 71 failed";}
	{var v := add(191, 93); expect v == 284, "test 72 failed";}
	{var v := add(125, 119); expect v == 244, "test 73 failed";}
	{var v := add(528, 936); expect v == 1464, "test 74 failed";}
	{var v := add(314, 7); expect v == 321, "test 75 failed";}
	{var v := add(270, 420); expect v == 690, "test 76 failed";}
	{var v := add(25, 435); expect v == 460, "test 77 failed";}
	{var v := add(876, 389); expect v == 1265, "test 78 failed";}
	{var v := add(502, 653); expect v == 1155, "test 79 failed";}
	{var v := add(519, 807); expect v == 1326, "test 80 failed";}
	{var v := add(345, 523); expect v == 868, "test 81 failed";}
	{var v := add(473, 231); expect v == 704, "test 82 failed";}
	{var v := add(746, 105); expect v == 851, "test 83 failed";}
	{var v := add(18, 434); expect v == 452, "test 84 failed";}
	{var v := add(659, 191); expect v == 850, "test 85 failed";}
	{var v := add(855, 65); expect v == 920, "test 86 failed";}
	{var v := add(843, 872); expect v == 1715, "test 87 failed";}
	{var v := add(997, 59); expect v == 1056, "test 88 failed";}
	{var v := add(420, 134); expect v == 554, "test 89 failed";}
	{var v := add(950, 85); expect v == 1035, "test 90 failed";}
	{var v := add(223, 50); expect v == 273, "test 91 failed";}
	{var v := add(473, 244); expect v == 717, "test 92 failed";}
	{var v := add(994, 169); expect v == 1163, "test 93 failed";}
	{var v := add(287, 494); expect v == 781, "test 94 failed";}
	{var v := add(528, 830); expect v == 1358, "test 95 failed";}
	{var v := add(492, 739); expect v == 1231, "test 96 failed";}
	{var v := add(483, 198); expect v == 681, "test 97 failed";}
	{var v := add(228, 863); expect v == 1091, "test 98 failed";}
	{var v := add(345, 405); expect v == 750, "test 99 failed";}
	{var v := add(878, 86); expect v == 964, "test 100 failed";}
	{var v := add(841, 854); expect v == 1695, "test 101 failed";}
	{var v := add(950, 134); expect v == 1084, "test 102 failed";}
	{var v := add(550, 501); expect v == 1051, "test 103 failed";}
	{var v := add(371, 167); expect v == 538, "test 104 failed";}
}