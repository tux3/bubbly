BEGIN {
    RS="},";
    N=0;
    E=0
}

{
    if ($4 == "2,") {
        E=1
    }
}

{
    if (E==1 && $3 == "\"hide_name\":" && $4 == "0,") {
        if (NAMES[$1] >= 0) {
            #print "##########",NAMES[$1], $1;
        } else {
            NAMES[$1]++;
        }
        newname = "z"N
        gsub("\".*\"", "\""newname"\"", $1);
        printf "%s {",$1;
        for(i=3;i<=NF;++i)
            printf "%s ", $i;
        print "},";
        N+=1
    } else {
        print $0,"},"
    }
}
