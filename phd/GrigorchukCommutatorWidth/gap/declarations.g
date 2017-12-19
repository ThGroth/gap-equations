f1 := (1,2)(3,6)(4,8)(5,7)(9,13)(10,12)(11,14)(15,16);
f2 := (1,3)(2,6)(4,9)(5,10)(7,12)(8,13)(11,15)(14,16);
f3 := (1,4)(2,7)(3,9)(5,11)(6,12)(8,14)(10,15)(13,16);
f4 := (1,5)(2,8)(3,10)(4,11)(6,13)(7,14)(9,15)(12,16);

Q := Group(f4,f2,f1,f1*f2);
QL := [	(),
		( 1, 5)( 2, 8)( 3,10)( 4,11)( 6,13)( 7,14)( 9,15)(12,16),
		( 1, 4)( 2, 7)( 3, 9)( 5,11)( 6,12)( 8,14)(10,15)(13,16),
		( 1,11)( 2,14)( 3,15)( 4, 5)( 6,16)( 7, 8)( 9,10)(12,13),
		( 1, 3)( 2, 6)( 4, 9)( 5,10)( 7,12)( 8,13)(11,15)(14,16),
		( 1,10)( 2,13)( 3, 5)( 4,15)( 6, 8)( 7,16)( 9,11)(12,14),
		( 1, 9)( 2,12)( 3, 4)( 5,15)( 6, 7)( 8,16)(10,11)(13,14),
		( 1,15)( 2,16)( 3,11)( 4,10)( 5, 9)( 6,14)( 7,13)( 8,12),
		( 1, 2)( 3, 6)( 4, 8)( 5, 7)( 9,13)(10,12)(11,14)(15,16),
		( 1, 8,11, 7)( 2, 5,14, 4)( 3,13,15,12)( 6,10,16, 9),
		( 1, 7,11, 8)( 2, 4,14, 5)( 3,12,15,13)( 6, 9,16,10),
		( 1,14)( 2,11)( 3,16)( 4, 7)( 5, 8)( 6,15)( 9,12)(10,13),
		( 1, 6)( 2, 3)( 4,13)( 5,12)( 7,10)( 8, 9)(11,16)(14,15),
		( 1,13,11,12)( 2,10,14, 9)( 3, 8,15, 7)( 4, 6, 5,16),
		( 1,12,11,13)( 2, 9,14,10)( 3, 7,15, 8)( 4,16, 5, 6),
		( 1,16)( 2,15)( 3,14)( 4,12)( 5,13)( 6,11)( 7, 9)( 8,10)];

GPmodKP := Group(
	[ (   1,  24, 177, 493, 927, 545, 225,  33)(   2,  15, 129, 441, 861, 590, 254,  41)(   3,  49, 283, 635, 807, 405, 109,  12)(   4,  57, 310, 678, 929, 585, 244,  39)
    (   5,  63, 318, 686, 928, 579, 239,  36)(   6,  69, 326, 694, 753, 369,  89,   9)(   7,  77, 353, 737, 863, 630, 273,  47)(   8,  83, 361, 745, 862, 624, 268,  44)
    (  10,  21, 163, 484, 920, 795, 395,  97)(  11,  18, 149, 475, 913, 801, 400, 103)(  13,  30, 211, 536, 986, 849, 431, 117)(  14,  27, 197, 527, 979, 855, 436, 123)
    (  16, 137, 467, 903, 696, 791, 387,  95)(  17, 143, 471, 908, 695, 787, 383,  92)(  19, 157, 332, 716, 922, 759, 391,  96)(  20, 146, 445, 872, 921, 601, 258, 100)
    (  22, 171, 447, 883, 915, 596, 279,  48)(  23,  86, 330, 705, 914, 764, 373, 106)(  25, 185, 519, 969, 637, 845, 423, 115)(  26, 191, 523, 974, 636, 841, 419, 112)
    (  28, 205, 289, 657, 988, 813, 427, 116)(  29, 194, 497, 938, 987, 556, 229, 120)(  31, 219, 499, 949, 981, 551, 250,  40)(  32,  66, 287, 646, 980, 818, 409, 126)
    (  34,  55, 301, 674, 809, 930, 571, 232)(  35,  52, 297, 669, 808, 932, 575, 234)(  37,  56, 306, 641, 999, 829, 411, 181)(  38,  60, 182, 504, 931, 994, 549, 236)
    (  42,  75, 344, 733, 755, 864, 616, 261)(  43,  72, 340, 728, 754, 866, 620, 263)(  45,  76, 349, 700,1007, 775, 375, 133)(  46,  80, 134, 452, 865,1002, 594, 265)
    (  50, 290, 661, 810, 495, 936, 563, 230)(  51, 292, 665, 812, 494, 934, 559, 228)(  53, 113, 184, 515, 933, 993, 567, 231)(  54, 294, 639,1009, 811, 416, 114, 188)
    (  58, 291, 643, 971, 688, 827, 425, 192)(  59, 193, 503, 937, 687, 970, 561, 241)(  61, 190, 322, 691,1011, 998, 584, 243)(  62, 315, 682,1010,1000, 587, 247, 189)
    (  64, 186, 501, 935, 680, 976, 565, 248)(  65, 293, 645, 975, 679, 823, 421, 187)(  67, 206, 314, 683, 951, 940, 588, 249)(  68, 323, 690, 939, 950, 582, 242, 207)
    (  70, 333, 720, 756, 443, 870, 608, 259)(  71, 335, 724, 758, 442, 868, 604, 257)(  73,  93, 136, 463, 867,1001, 612, 260)(  74, 337, 698,1013, 757, 380,  94, 140)
    (  78, 334, 702, 905, 747, 773, 389, 144)(  79, 145, 451, 871, 746, 904, 606, 270)(  81, 142, 365, 750,1015,1006, 629, 272)(  82, 358, 741,1014,1008, 632, 276, 141)
    (  84, 138, 449, 869, 739, 910, 610, 277)(  85, 336, 704, 909, 738, 769, 385, 139)(  87, 158, 357, 742, 885, 874, 633, 278)(  88, 366, 749, 873, 884, 627, 271, 159)
    (  90, 135, 459, 899, 592, 697, 779, 376)(  91, 132, 455, 895, 591, 699, 783, 378)(  98, 155, 347, 714, 803, 923, 761, 377)(  99, 152, 457, 877, 802, 925, 600, 264)
    ( 101, 156, 481, 919,1018, 806, 402, 167)( 102, 160, 168, 487, 924,1017, 798, 399)( 104, 169, 461, 881, 797, 916, 598, 262)( 105, 166, 342, 710, 796, 918, 763, 379)
    ( 107, 170, 490, 926,1004, 799, 398, 153)( 108, 174, 154, 478, 917,1003, 805, 403)( 110, 183, 511, 965, 547, 638, 833, 412)( 111, 180, 507, 961, 546, 640, 837, 414)
    ( 118, 203, 304, 655, 857, 989, 815, 413)( 119, 200, 509, 943, 856, 991, 555, 235)( 121, 204, 533, 985,1021, 860, 438, 215)( 122, 208, 216, 539, 990,1020, 852, 435)
    ( 124, 217, 513, 947, 851, 982, 553, 233)( 125, 214, 299, 651, 850, 984, 817, 415)( 127, 218, 542, 992, 996, 853, 434, 201)( 128, 222, 202, 530, 983, 995, 859, 439)
    ( 130, 448, 887, 593, 328, 703, 771, 374)( 131, 450, 891, 595, 327, 701, 767, 372)( 147, 172, 470, 906, 718, 707, 793, 390)( 148, 473, 912, 706, 717, 789, 386, 173)
    ( 150, 356, 713, 804, 486, 748, 772, 397)( 151, 474, 876, 631, 485, 907, 623, 269)( 161, 176, 466, 886,1023,1005, 615, 282)( 162, 352, 719,1016,1019, 778, 394, 175)
    ( 164, 469, 880, 744, 477, 911, 609, 367)( 165, 368, 709, 792, 476, 743, 786, 384)( 178, 500, 953, 548, 285, 644, 825, 410)( 179, 502, 957, 550, 284, 642, 821, 408)
    ( 195, 220, 522, 972, 659, 648, 847, 426)( 196, 525, 978, 647, 658, 843, 422, 221)( 198, 313, 654, 858, 538, 689, 826, 433)( 199, 526, 942, 586, 537, 973, 578, 240)
    ( 209, 224, 518, 952,1024, 997, 570, 253)( 210, 309, 660,1012,1022, 832, 430, 223)( 212, 521, 946, 685, 529, 977, 564, 324)( 213, 325, 650, 846, 528, 684, 840, 420)
    ( 226, 288, 653, 816, 407, 496, 941, 552)( 227, 286, 649, 814, 406, 498, 945, 554)( 237, 305, 676, 820, 831, 944, 574, 251)( 238, 252, 300, 672, 830, 819, 948, 577)
    ( 245, 321, 512, 955, 581, 681, 962, 573)( 246, 298, 668, 854, 580, 675, 822, 440)( 255, 331, 712, 762, 371, 444, 875, 597)( 256, 329, 708, 760, 370, 446, 879, 599)
    ( 266, 348, 735, 766, 777, 878, 619, 280)( 267, 281, 343, 731, 776, 765, 882, 622)( 274, 364, 460, 889, 626, 740, 896, 618)( 275, 341, 727, 800, 625, 734, 768, 404)
    ( 295, 307, 664, 824, 517, 506, 959, 566)( 296, 667, 828, 505, 516, 956, 562, 308)( 302, 663, 842, 693, 671, 835, 424, 316)( 303, 317, 508, 960, 670, 692, 966, 560)
    ( 311, 662, 838, 437, 320, 666, 834, 432)( 312, 524, 958, 572, 319, 520, 954, 576)( 338, 350, 723, 770, 465, 454, 893, 611)( 339, 726, 774, 453, 464, 890, 607, 351)
    ( 345, 722, 788, 752, 730, 781, 388, 359)( 346, 360, 456, 894, 729, 751, 900, 605)( 354, 721, 784, 401, 363, 725, 780, 396)( 355, 472, 892, 617, 362, 468, 888, 621)
    ( 381, 462, 901, 603, 614, 711, 782, 392)( 382, 393, 458, 897, 613, 602, 715, 785)( 417, 514, 967, 558, 569, 652, 836, 428)( 418, 429, 510, 963, 568, 557, 656, 839)
    ( 479, 482, 736, 790, 492, 489, 732, 794)( 480, 898, 634, 488, 491, 902, 628, 483)( 531, 534, 677, 844, 544, 541, 673, 848)( 532, 964, 589, 540, 543, 968, 583, 535), 
  (   1, 235, 954, 217)(   2, 264, 888, 169)(   3, 125, 838, 304)(   4, 128, 821, 305)(   5, 238, 953, 218)(   6, 105, 784, 347)(   7, 108, 767, 348)(   8, 267, 887, 170)
    (   9, 379, 721, 155)(  10, 263, 879, 135)(  11, 378, 712,  75)(  12, 415, 662, 203)(  13, 234, 945, 183)(  14, 414, 653,  55)(  15,  99, 621, 461)(  16, 102, 604, 462)
    (  17, 382, 720, 156)(  18,  91, 762, 344)(  19,  94, 786, 345)(  20, 346, 880, 136)(  21,  43, 599, 459)(  22,  46, 623, 460)(  23, 404, 713,  76)(  24, 119, 576, 513)
    (  25, 122, 559, 514)(  26, 418, 661, 204)(  27, 111, 816, 301)(  28, 114, 840, 302)(  29, 303, 946, 184)(  30,  35, 554, 511)(  31,  38, 578, 512)(  32, 440, 654,  56)
    (  33, 555, 520, 124)(  34, 123, 837, 288)(  36, 577, 500, 127)(  37, 126, 822, 313)(  39, 439, 642, 237)(  40, 236, 973, 321)(  41, 600, 468, 104)(  42, 103, 783, 331)
    (  44, 622, 448, 107)(  45, 106, 768, 356)(  47, 403, 701, 266)(  48, 265, 907, 364)(  49, 214, 437, 655)(  50, 215, 419, 656)(  51, 558, 519, 216)(  52, 227, 965, 211)
    (  53, 229, 966, 212)(  54, 213, 842, 289)(  57, 222, 408, 676)(  58, 223, 421, 677)(  59, 583, 501, 224)(  60, 240, 955, 219)(  61, 242, 956, 220)(  62, 221, 824, 314)
    (  63, 252, 548, 542)(  64, 253, 561, 543)(  65, 544, 643, 309)(  66, 246, 858, 306)(  67, 247, 843, 307)(  68, 308, 972, 322)(  69, 166, 401, 714)(  70, 167, 383, 715)
    (  71, 603, 467, 168)(  72, 256, 899, 163)(  73, 258, 900, 164)(  74, 165, 788, 332)(  77, 174, 372, 735)(  78, 175, 385, 736)(  79, 628, 449, 176)(  80, 269, 889, 171)
    (  81, 271, 890, 172)(  82, 173, 770, 357)(  83, 281, 593, 490)(  84, 282, 606, 491)(  85, 492, 702, 352)(  86, 275, 804, 349)(  87, 276, 789, 350)(  88, 351, 906, 365)
    (  89, 763, 354,  98)(  90,  97, 620, 446)(  92, 785, 333, 101)(  93, 100, 605, 469)(  95, 399, 868, 381)(  96, 380, 743, 359)( 109, 817, 311, 118)( 110, 117, 575, 498)
    ( 112, 839, 290, 121)( 113, 120, 560, 521)( 115, 435, 934, 417)( 116, 416, 684, 316)( 129, 152, 355, 881)( 130, 153, 268, 882)( 131, 766, 353, 154)( 132, 371, 733, 149)
    ( 133, 373, 734, 150)( 134, 151, 626, 447)( 137, 160, 257, 901)( 138, 161, 270, 902)( 139, 790, 334, 162)( 140, 384, 722, 157)( 141, 386, 723, 158)( 142, 159, 607, 470)
    ( 143, 393, 756, 481)( 144, 394, 769, 482)( 145, 483, 869, 466)( 146, 360, 744, 463)( 147, 272, 627, 464)( 148, 465, 742, 358)( 177, 200, 312, 947)( 178, 201, 239, 948)
    ( 179, 820, 310, 202)( 180, 407, 674, 197)( 181, 409, 675, 198)( 182, 199, 581, 499)( 185, 208, 228, 967)( 186, 209, 241, 968)( 187, 844, 291, 210)( 188, 420, 663, 205)
    ( 189, 422, 664, 206)( 190, 207, 562, 522)( 191, 429, 810, 533)( 192, 430, 823, 534)( 193, 535, 935, 518)( 194, 317, 685, 515)( 195, 243, 582, 516)( 196, 517, 683, 315)
    ( 225, 991, 319, 233)( 226, 232, 436, 640)( 230, 438, 841, 557)( 231, 556, 692, 324)( 244, 859, 284, 251)( 245, 250, 549, 537)( 248, 570, 970, 540)( 249, 587, 658, 295)
    ( 254, 925, 362, 262)( 255, 261, 400, 699)( 259, 402, 787, 602)( 260, 601, 751, 367)( 273, 805, 327, 280)( 274, 279, 594, 485)( 277, 615, 904, 488)( 278, 632, 717, 338)
    ( 283, 299, 320, 857)( 285, 992, 318, 300)( 286, 547, 536, 297)( 287, 298, 538, 641)( 292, 569, 969, 539)( 293, 541, 971, 660)( 294, 325, 693, 657)( 296, 659, 691, 323)
    ( 326, 342, 363, 803)( 328, 926, 361, 343)( 329, 592, 484, 340)( 330, 341, 486, 700)( 335, 614, 903, 487)( 336, 489, 905, 719)( 337, 368, 752, 716)( 339, 718, 750, 366)
    ( 369, 918, 396, 377)( 370, 376, 395, 866)( 374, 398, 624, 765)( 375, 764, 625, 397)( 387, 798, 442, 392)( 388, 391, 757, 476)( 389, 778, 738, 479)( 390, 629, 884, 453)
    ( 405, 984, 432, 413)( 406, 412, 431, 932)( 410, 434, 579, 819)( 411, 818, 580, 433)( 423, 852, 494, 428)( 424, 427, 811, 528)( 425, 832, 679, 531)( 426, 584, 950, 505)
    ( 441, 457, 472, 797)( 443, 919, 471, 458)( 444, 755, 475, 455)( 445, 456, 477, 867)( 450, 777, 737, 478)( 451, 480, 739, 886)( 452, 474, 740, 883)( 454, 885, 741, 473)
    ( 493, 509, 524, 851)( 495, 985, 523, 510)( 496, 809, 527, 507)( 497, 508, 529, 933)( 502, 831, 678, 530)( 503, 532, 680, 952)( 504, 526, 681, 949)( 506, 951, 682, 525)
    ( 545, 856, 572, 553)( 546, 552, 571, 855)( 550, 574, 585, 995)( 551, 994, 586, 573)( 563, 860, 636, 568)( 564, 567, 987, 670)( 565, 997, 687, 589)( 566, 588,1000, 647)
    ( 590, 802, 617, 598)( 591, 597, 616, 801)( 595, 619, 630,1003)( 596,1002, 631, 618)( 608, 806, 695, 613)( 609, 612, 921, 729)( 610,1005, 746, 634)( 611, 633,1008, 706)
    ( 635, 651, 666, 989)( 637, 990, 665, 652)( 638, 986, 669, 649)( 639, 650, 671, 988)( 644, 996, 686, 672)( 645, 673, 688,1012)( 646, 668, 689, 999)( 648,1011, 690, 667)
    ( 694, 710, 725, 923)( 696, 924, 724, 711)( 697, 920, 728, 708)( 698, 709, 730, 922)( 703,1004, 745, 731)( 704, 732, 747,1016)( 705, 727, 748,1007)( 707,1015, 749, 726)
    ( 753, 796, 780, 761)( 754, 760, 779, 795)( 758, 782, 791,1017)( 759,1013, 792, 781)( 771, 799, 862, 776)( 772, 775, 914, 800)( 773,1019, 909, 794)( 774, 793,1006, 873)
    ( 807, 850, 834, 815)( 808, 814, 833, 849)( 812, 836, 845,1020)( 813,1009, 846, 835)( 825, 853, 928, 830)( 826, 829, 980, 854)( 827,1022, 975, 848)( 828, 847, 998, 939)
    ( 861, 877, 892, 916)( 863, 917, 891, 878)( 864, 913, 895, 875)( 865, 876, 896, 915)( 870,1018, 908, 897)( 871, 898, 910,1023)( 872, 894, 911,1001)( 874,1014, 912, 893)
    ( 927, 943, 958, 982)( 929, 983, 957, 944)( 930, 979, 961, 941)( 931, 942, 962, 981)( 936,1021, 974, 963)( 937, 964, 976,1024)( 938, 960, 977, 993)( 940,1010, 978, 959),
  (   1, 193, 958, 248)(   2, 145, 892, 277)(   3, 293, 834, 192)(   4, 191, 957, 230)(   5, 292, 825, 115)(   6, 336, 780, 144)(   7, 143, 891, 259)(   8, 335, 771,  95)
    (   9,  85, 725, 389)(  10,  88, 708, 390)(  11, 148, 875, 278)(  12,  65, 666, 425)(  13,  68, 649, 426)(  14, 196, 941, 249)(  15, 451, 617,  84)(  16,  83, 724, 374)
    (  17, 450, 608,  47)(  18, 473, 597,  87)(  19,  86, 709, 397)(  20, 474, 609,  48)(  21, 366, 760, 147)(  22, 146, 876, 367)(  23, 368, 772,  96)(  24, 503, 572,  64)
    (  25,  63, 665, 410)(  26, 502, 563,  39)(  27, 525, 552,  67)(  28,  66, 650, 433)(  29, 526, 564,  40)(  30, 323, 814, 195)(  31, 194, 942, 324)(  32, 325, 826, 116)
    (  33,  59, 524, 565)(  34,  62, 507, 566)(  35, 296, 833, 243)(  36,  51, 644, 423)(  37,  54, 668, 424)(  38, 317, 962, 231)(  41,  79, 472, 610)(  42,  82, 455, 611)
    (  43, 339, 779, 272)(  44,  71, 703, 387)(  45,  74, 727, 388)(  46, 360, 896, 260)(  49, 645, 432,  58)(  50,  57, 523, 550)(  52, 667, 412,  61)(  53,  60, 508, 573)
    (  55, 315, 961, 295)(  56, 294, 854, 316)(  69, 704, 396,  78)(  70,  77, 471, 595)(  72, 726, 376,  81)(  73,  80, 456, 618)(  75, 358, 895, 338)(  76, 337, 800, 359)
    (  89, 139, 363, 773)(  90, 142, 340, 774)(  91, 454, 616, 276)(  92, 131, 870, 273)(  93, 134, 894, 274)(  94, 275, 730, 375)(  97, 159, 329, 793)(  98, 162, 342, 794)
    (  99, 480, 598, 282)( 100, 151, 911, 279)( 101, 154, 897, 280)( 102, 281, 711, 398)( 103, 173, 444, 633)( 104, 176, 457, 634)( 105, 489, 761, 394)( 106, 165, 748, 391)
    ( 107, 168, 731, 392)( 108, 393, 878, 402)( 109, 187, 320, 827)( 110, 190, 297, 828)( 111, 506, 571, 247)( 112, 179, 936, 244)( 113, 182, 960, 245)( 114, 246, 671, 411)
    ( 117, 207, 286, 847)( 118, 210, 299, 848)( 119, 532, 553, 253)( 120, 199, 977, 250)( 121, 202, 963, 251)( 122, 252, 652, 434)( 123, 221, 496, 588)( 124, 224, 509, 589)
    ( 125, 541, 815, 430)( 126, 213, 689, 427)( 127, 216, 672, 428)( 128, 429, 944, 438)( 129, 871, 362, 138)( 130, 137, 361, 758)( 132, 893, 261, 141)( 133, 140, 341, 781)
    ( 135, 365, 728, 453)( 136, 452, 729, 364)( 149, 912, 255, 158)( 150, 157, 330, 792)( 152, 898, 262, 161)( 153, 160, 343, 782)( 155, 352, 710, 479)( 156, 478, 613, 266)
    ( 163, 749, 370, 172)( 164, 171, 445, 631)( 166, 732, 377, 175)( 167, 174, 458, 619)( 169, 466, 877, 488)( 170, 487, 776, 381)( 177, 937, 319, 186)( 178, 185, 318, 812)
    ( 180, 959, 232, 189)( 181, 188, 298, 835)( 183, 322, 669, 505)( 184, 504, 670, 321)( 197, 978, 226, 206)( 198, 205, 287, 846)( 200, 964, 233, 209)( 201, 208, 300, 836)
    ( 203, 309, 651, 531)( 204, 530, 568, 237)( 211, 690, 406, 220)( 212, 219, 497, 586)( 214, 673, 413, 223)( 215, 222, 510, 574)( 217, 518, 943, 540)( 218, 539, 830, 417)
    ( 225, 241, 312, 976)( 227, 648, 431, 242)( 228, 285, 845, 239)( 229, 240, 529, 551)( 234, 308, 638, 584)( 235, 535, 982, 570)( 236, 303, 681, 567)( 238, 569, 853, 435)
    ( 254, 270, 355, 910)( 256, 707, 395, 271)( 257, 328, 791, 268)( 258, 269, 477, 596)( 263, 351, 697, 629)( 264, 483, 916, 615)( 265, 346, 740, 612)( 267, 614, 799, 399)
    ( 283, 975, 311, 291)( 284, 290, 310, 974)( 288, 314, 527, 647)( 289, 646, 528, 313)( 301, 682, 546, 307)( 302, 306, 639, 580)( 304, 660, 850, 534)( 305, 533, 983, 557)
    ( 326, 909, 354, 334)( 327, 333, 353, 908)( 331, 357, 475, 706)( 332, 705, 476, 356)( 344, 741, 591, 350)( 345, 349, 698, 625)( 347, 719, 796, 482)( 348, 481, 917, 602)
    ( 369, 385, 401, 747)( 371, 874, 400, 386)( 372, 443, 630, 383)( 373, 384, 486, 759)( 378, 465, 864, 632)( 379, 492, 923, 778)( 380, 404, 752, 775)( 382, 777, 806, 403)
    ( 405, 421, 437, 688)( 407, 940, 436, 422)( 408, 495, 585, 419)( 409, 420, 538, 813)( 414, 517, 930, 587)( 415, 544, 989, 832)( 416, 440, 693, 829)( 418, 831, 860, 439)
    ( 441, 746, 468, 449)( 442, 448, 467, 745)( 446, 470, 484, 873)( 447, 872, 485, 469)( 459, 750, 754, 464)( 460, 463, 865, 751)( 461, 886, 802, 491)( 462, 490, 924, 765)
    ( 493, 687, 520, 501)( 494, 500, 519, 686)( 498, 522, 536, 939)( 499, 938, 537, 521)( 511, 691, 808, 516)( 512, 515, 931, 692)( 513, 952, 856, 543)( 514, 542, 990, 819)
    ( 545, 561, 576, 680)( 547, 998, 575, 562)( 548, 637, 579, 559)( 549, 560, 581, 993)( 554, 659, 849, 582)( 555, 583, 851, 997)( 556, 578, 685, 981)( 558, 996, 852, 577)
    ( 590, 606, 621, 739)( 592,1006, 620, 607)( 593, 696, 624, 604)( 594, 605, 626,1001)( 599, 718, 795, 627)( 600, 628, 797,1005)( 601, 623, 744, 915)( 603,1004, 798, 622)
    ( 635, 679, 662, 643)( 636, 642, 661, 678)( 640, 664, 674,1010)( 641,1009, 675, 663)( 653, 683, 979, 658)( 654, 657, 980, 684)( 655,1012, 984, 677)( 656, 676, 985, 995)
    ( 694, 738, 721, 702)( 695, 701, 720, 737)( 699, 723, 733,1014)( 700,1013, 734, 722)( 712, 742, 913, 717)( 713, 716, 914, 743)( 714,1016, 918, 736)( 715, 735, 919,1003)
    ( 753, 769, 784, 905)( 755,1008, 783, 770)( 756, 863, 787, 767)( 757, 768, 788,1007)( 762, 885, 801, 789)( 763, 790, 803,1019)( 764, 786, 804, 922)( 766,1018, 805, 785)
    ( 807, 823, 838, 971)( 809,1000, 837, 824)( 810, 929, 841, 821)( 811, 822, 842, 999)( 816, 951, 855, 843)( 817, 844, 857,1022)( 818, 840, 858, 988)( 820,1021, 859, 839)
    ( 861, 904, 888, 869)( 862, 868, 887, 903)( 866, 890, 899,1015)( 867,1002, 900, 889)( 879, 906, 920, 884)( 880, 883, 921, 907)( 881,1023, 925, 902)( 882, 901, 926,1017)
    ( 927, 970, 954, 935)( 928, 934, 953, 969)( 932, 956, 965,1011)( 933, 994, 966, 955)( 945, 972, 986, 950)( 946, 949, 987, 973)( 947,1024, 991, 968)( 948, 967, 992,1020),
  (   1,  32)(   2,  23)(   3,  38)(   4,  35)(   5,  14)(   6,  46)(   7,  43)(   8,  11)(   9,  20)(  10,  17)(  12,  29)(  13,  26)(  15,  94)(  16,  91)(  18, 102)
    (  19,  99)(  21, 108)(  22, 105)(  24, 114)(  25, 111)(  27, 122)(  28, 119)(  30, 128)(  31, 125)(  33,  54)(  34,  51)(  36,  62)(  37,  59)(  39,  68)(  40,  65)
    (  41,  74)(  42,  71)(  44,  82)(  45,  79)(  47,  88)(  48,  85)(  49, 229)(  50, 227)(  52, 215)(  53, 214)(  55, 238)(  56, 235)(  57, 242)(  58, 240)(  60, 223)
    (  61, 222)(  63, 247)(  64, 246)(  66, 253)(  67, 252)(  69, 258)(  70, 256)(  72, 167)(  73, 166)(  75, 267)(  76, 264)(  77, 271)(  78, 269)(  80, 175)(  81, 174)
    (  83, 276)(  84, 275)(  86, 282)(  87, 281)(  89, 134)(  90, 131)(  92, 142)(  93, 139)(  95, 148)(  96, 145)(  97, 154)(  98, 151)( 100, 162)( 101, 159)( 103, 168)
    ( 104, 165)( 106, 176)( 107, 173)( 109, 182)( 110, 179)( 112, 190)( 113, 187)( 115, 196)( 116, 193)( 117, 202)( 118, 199)( 120, 210)( 121, 207)( 123, 216)( 124, 213)
    ( 126, 224)( 127, 221)( 129, 373)( 130, 371)( 132, 153)( 133, 152)( 135, 382)( 136, 379)( 137, 386)( 138, 384)( 140, 161)( 141, 160)( 143, 272)( 144, 360)( 146, 394)
    ( 147, 393)( 149, 268)( 150, 355)( 155, 346)( 156, 263)( 157, 270)( 158, 257)( 163, 383)( 164, 401)( 169, 404)( 170, 378)( 171, 385)( 172, 372)( 177, 409)( 178, 407)
    ( 180, 201)( 181, 200)( 183, 418)( 184, 415)( 185, 422)( 186, 420)( 188, 209)( 189, 208)( 191, 243)( 192, 317)( 194, 430)( 195, 429)( 197, 239)( 198, 312)( 203, 303)
    ( 204, 234)( 205, 241)( 206, 228)( 211, 419)( 212, 437)( 217, 440)( 218, 414)( 219, 421)( 220, 408)( 225, 287)( 226, 285)( 230, 296)( 231, 293)( 232, 300)( 233, 298)
    ( 236, 309)( 237, 308)( 244, 297)( 245, 320)( 248, 325)( 249, 292)( 250, 299)( 251, 286)( 254, 330)( 255, 328)( 259, 339)( 260, 336)( 261, 343)( 262, 341)( 265, 352)
    ( 266, 351)( 273, 340)( 274, 363)( 277, 368)( 278, 335)( 279, 342)( 280, 329)( 283, 549)( 284, 547)( 288, 558)( 289, 555)( 290, 562)( 291, 560)( 294, 570)( 295, 569)
    ( 301, 559)( 302, 576)( 304, 578)( 305, 554)( 306, 561)( 307, 548)( 310, 575)( 311, 581)( 313, 583)( 314, 577)( 315, 435)( 316, 535)( 318, 436)( 319, 538)( 321, 544)
    ( 322, 439)( 323, 438)( 324, 541)( 326, 594)( 327, 592)( 331, 603)( 332, 600)( 333, 607)( 334, 605)( 337, 615)( 338, 614)( 344, 604)( 345, 621)( 347, 623)( 348, 599)
    ( 349, 606)( 350, 593)( 353, 620)( 354, 626)( 356, 628)( 357, 622)( 358, 399)( 359, 483)( 361, 400)( 362, 486)( 364, 492)( 365, 403)( 366, 402)( 367, 489)( 369, 445)
    ( 370, 443)( 374, 454)( 375, 451)( 376, 458)( 377, 456)( 380, 466)( 381, 465)( 387, 455)( 388, 472)( 389, 474)( 390, 450)( 391, 457)( 392, 444)( 395, 471)( 396, 477)
    ( 397, 480)( 398, 473)( 405, 497)( 406, 495)( 410, 506)( 411, 503)( 412, 510)( 413, 508)( 416, 518)( 417, 517)( 423, 507)( 424, 524)( 425, 526)( 426, 502)( 427, 509)
    ( 428, 496)( 431, 523)( 432, 529)( 433, 532)( 434, 525)( 441, 757)( 442, 755)( 446, 766)( 447, 763)( 448, 770)( 449, 768)( 452, 778)( 453, 777)( 459, 767)( 460, 784)
    ( 461, 786)( 462, 762)( 463, 769)( 464, 756)( 467, 783)( 468, 788)( 469, 790)( 470, 785)( 475, 798)( 476, 797)( 478, 629)( 479, 740)( 481, 627)( 482, 744)( 484, 805)
    ( 485, 803)( 487, 632)( 488, 752)( 490, 789)( 491, 804)( 493, 811)( 494, 809)( 498, 820)( 499, 817)( 500, 824)( 501, 822)( 504, 832)( 505, 831)( 511, 821)( 512, 838)
    ( 513, 840)( 514, 816)( 515, 823)( 516, 810)( 519, 837)( 520, 842)( 521, 844)( 522, 839)( 527, 852)( 528, 851)( 530, 584)( 531, 681)( 533, 582)( 534, 685)( 536, 859)
    ( 537, 857)( 539, 587)( 540, 693)( 542, 843)( 543, 858)( 545, 639)( 546, 637)( 550, 648)( 551, 645)( 552, 652)( 553, 650)( 556, 660)( 557, 659)( 563, 649)( 564, 666)
    ( 565, 668)( 566, 644)( 567, 651)( 568, 638)( 571, 665)( 572, 671)( 573, 673)( 574, 667)( 579, 682)( 580, 680)( 585, 690)( 586, 688)( 588, 672)( 589, 689)( 590, 698)
    ( 591, 696)( 595, 707)( 596, 704)( 597, 711)( 598, 709)( 601, 719)( 602, 718)( 608, 708)( 609, 725)( 610, 727)( 611, 703)( 612, 710)( 613, 697)( 616, 724)( 617, 730)
    ( 618, 732)( 619, 726)( 624, 741)( 625, 739)( 630, 749)( 631, 747)( 633, 731)( 634, 748)( 635, 987)( 636, 986)( 640, 992)( 641, 991)( 642, 972)( 643, 973)( 646, 997)
    ( 647, 996)( 653, 953)( 654, 954)( 655, 966)( 656, 965)( 657, 970)( 658, 969)( 661, 945)( 662, 946)( 663, 968)( 664, 967)( 669, 860)( 670, 989)( 674, 948)( 675, 947)
    ( 676, 956)( 677, 955)( 678, 950)( 679, 949)( 683, 934)( 684, 935)( 686,1000)( 687, 999)( 691, 841)( 692, 971)( 694, 921)( 695, 920)( 699, 926)( 700, 925)( 701, 906)
    ( 702, 907)( 705,1005)( 706,1004)( 712, 887)( 713, 888)( 714, 900)( 715, 899)( 716, 904)( 717, 903)( 720, 879)( 721, 880)( 722, 902)( 723, 901)( 728, 806)( 729, 923)
    ( 733, 882)( 734, 881)( 735, 890)( 736, 889)( 737, 884)( 738, 883)( 742, 868)( 743, 869)( 745,1008)( 746,1007)( 750, 787)( 751, 905)( 753, 865)( 754, 863)( 758, 874)
    ( 759, 871)( 760, 878)( 761, 876)( 764, 886)( 765, 885)( 771, 875)( 772, 892)( 773, 894)( 774, 870)( 775, 877)( 776, 864)( 779, 891)( 780, 896)( 781, 898)( 782, 893)
    ( 791, 912)( 792, 910)( 793, 897)( 794, 911)( 795, 917)( 796, 915)( 799, 895)( 800, 916)( 801, 924)( 802, 922)( 807, 931)( 808, 929)( 812, 940)( 813, 937)( 814, 944)
    ( 815, 942)( 818, 952)( 819, 951)( 825, 941)( 826, 958)( 827, 960)( 828, 936)( 829, 943)( 830, 930)( 833, 957)( 834, 962)( 835, 964)( 836, 959)( 845, 978)( 846, 976)
    ( 847, 963)( 848, 977)( 849, 983)( 850, 981)( 853, 961)( 854, 982)( 855, 990)( 856, 988)( 861, 914)( 862, 913)( 866, 919)( 867, 918)( 872,1019)( 873,1018)( 908,1006)
    ( 909,1001)( 927, 980)( 928, 979)( 932, 985)( 933, 984)( 938,1022)( 939,1021)( 974, 998)( 975, 993)( 994,1012)( 995,1011)(1002,1016)(1003,1015)(1009,1024)(1010,1020)
    (1013,1023)(1014,1017) ]);
DeclarationsLoaded := true;