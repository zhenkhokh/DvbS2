import java.util.*;

abstract class A implements S2m, S2t, S2xSOF, S2xE, S2xType {abstract protected boolean isS2();}
interface S2m {    int getModCod();}
interface S2t {    int getType();}
interface S2xSOF {    int getPDistance();    int getPSize();    int getSFL();}
interface S2xE { int getSize(); int getSpread(); boolean isSF(); boolean isTrackedPlh(); boolean isSheduledBHSC();}
interface S2xType {    boolean isReserved();}
class U2 implements S2t {
    private int type;
    public U2(int type) {
        this.type = type & 0x3;
    }
    @Override
    public int getType() {
        return type;
    }
}
class U3 implements S2t, S2xType {
    private int type;
    private boolean isReserved;
    public U3(int type) {
        this.type = type & 0x7;
        isReserved = type != this.type;
    }
    @Override    public int getType() {
        return type;
    }
    @Override    public boolean isReserved() {        return isReserved;    }
}
class SFFI {
    private int type;
    private boolean isSuperFormat;

    public SFFI(int type) {
        this.type = type & 0xF;
        isSuperFormat = this.type == type;
    }
    public int getType() {
        return type;
    }
    public boolean isSF() {
        return isSuperFormat;
    }
}
class U5 implements S2m {
    private int modcod;
    public U5(int modcod) {
        this.modcod = modcod & 0x1F;
    }
    @Override    public int getModCod() {
        return modcod;
    }
}
class U8  {
    private int pls;
    public U8(int pls) {        this.pls = pls & 0xFF;    }
    public int toDec() {
        return pls;
    }
}
class SOF implements S2xSOF {
    private int dsf = 16, psf = 36, sfl = 612540;
    public SOF(int dsf, int psf, int sfl) {
        this(sfl);
        this.dsf = dsf;
        this.psf = psf;
    }
    public SOF(int sfl) {
        this.sfl = sfl * 1476;
    }
    public SOF() {
    }
    @Override    public int getPDistance() {        return dsf;    }
    @Override    public int getPSize() {        return psf;    }
    @Override    public int getSFL() {        return sfl;    }
}
class SFH {
    private int hPointer, pli, sfPilot;
    public SFH(int hPointer, int pli, int sfPilot) {
        this.hPointer = hPointer & 0x7FF;
        this.pli = (pli & 0x3) == 0 ? 5 : (pli & 0x3) == 1 ? 2 : 1;
        this.sfPilot = sfPilot & 0x1;
    }
    public int getHPointer() {        return hPointer;    }
    public int getPli() {        return pli;    }
    public int getSFPilot() {        return sfPilot;    }
}
class B extends A {
    static int MEDIUM = 0x0, NORMAL = 0x4, SHORT = 0x2, PILOT = 0x1;
    private boolean _isS2 = true;    
    private U3 typeX = new U3(-1);
    private SFFI eFormat = new SFFI(-1);
    private U8 s2xPls = new U8(-1);
    private int spread = 1, size = 16200, modcod = 0;
    private S2xSOF sf = new SOF();
    private SFH sfh = null; // use null in 0,1,2,3 formats
    private class AtE9 {
        List<Integer> e9pls = Arrays.asList(114, 116, 118, 120, 122, 124, 126, 176, 128, 130,254,188);
        public int getModCod() {
            return is() ? (PLSToDec() >= 128 ? (PLSToDec() & 0x7E) >> 1 : PLSToDec() >> 1) : -1;
        }
        public int getType() {
            return is() ? (PLSToDec() == 114 || PLSToDec() == 176
                    ? MEDIUM : PLSToDec() % 4 == 0 ? NORMAL : SHORT) : -1;
        }
        public boolean is() {            return e9pls.contains(s2xPls.toDec());        }
        public int spreadCode() {            return PLSToDec() <= 127 ? 0 : 1;        }
    }
    private AtE9 atE9 = new AtE9();
    private class AtE6 {
        public boolean is() {return  s2xPls.toDec() >= 64 && s2xPls.toDec() <=127;}
    }
    private AtE6 atE6 = new AtE6();
    protected boolean accept(U8 pls, int eFormat) {
        s2xPls = pls;
        int _modcod = pls.toDec()>>2;
        if (_modcod <= 31 && eFormat>=5)
            return accept(new U5(_modcod), new U2(pls.toDec()));//12
        else if (_modcod <= 15 && eFormat==4)
            return accept(new U5(pls.toDec()>>1),new U2(pls.toDec()<<1));//b7 is ignored
        accept(pls);
        int pilot = PLSToDec() & PILOT;
        int typeX = pilot | NORMAL;
        boolean table17aIn5_5_2_2Short = PLSToDec() < 250 && PLSToDec() >= 215;
        typeX = table17aIn5_5_2_2Short ? SHORT | pilot : typeX;
        boolean table17bIn5_5_2_2 = PLSToDec() >= 250;
        typeX = table17bIn5_5_2_2 ? NORMAL | pilot : typeX;
        this.modcod = (PLSToDec() & 0x7E) >> 1; //defined pls from 17a,b, b7 is ignored
        this.size = table17aIn5_5_2_2Short ? 16200 : 64800;
        this.typeX = new U3(typeX);
        return true;
    }
    protected boolean accept(U5 modcod) {        
        this.modcod = modcod.getModCod();
        return true;
    }
    protected boolean accept(U5 modcod, U2 type) {
        accept(modcod);
        this.typeX = new U3(type.getType());
        this.size = (getType() & 0x2) == SHORT ? 16200 : 64800;        
        return false;
    }
    private boolean accept(U8 pls) {
        s2xPls = pls;
        _isS2 = false;
        return true;
    }
    private int up(int from, int length) {
        from  = PLSToDec()  - from;
        if (from < 0)
            return -1;
        return from/length;
    }
    private static final int S = 4, s=2;
    private boolean isQPSK() {
        int mod = PLSToDec() > 127 ? (getType() == NORMAL ? up(132,6) :
                up(216,12)) : PLSToDec() <= 63 ? up(s,11*s) : up(64,16);
        return mod == 0;
    }
    private boolean is8PSK() {
                int mod = PLSToDec() > 127 ? (getType() == NORMAL ? up(138, 10):
                up(228,8)) : PLSToDec() <= 63 ? up(12*s, 6*s) : up(80,8);
        return mod == 0;
    }
    private boolean is16PSK() {
        int mod = PLSToDec() > 127 ? (getType() == NORMAL ? up(148,26) :
                up(236,10)) : PLSToDec()<= 63 ? up(18*s,6*s) : up(88,8);
        return mod == 0;
    }
    private boolean is32APSK() {
        int mod = PLSToDec() > 127 ? (getType() == NORMAL ? up(174,8) :
                up(246,4)) : PLSToDec() <= 63 ? up(24*s,5*s) : up(96,8);
        return mod == 0;
    }
    private boolean isQPSK5F() {
        int mod = atE9.is() ? 0 : PLSToDec() > 127 ? (getType() == NORMAL
                ? up(132,6) : up(216,12)) : PLSToDec() <= 127 ? up(S,11*S) : -1;
        return mod == 0;
    }
    private boolean is8PSK5F() {
        int mod = atE9.is() ? -1 : PLSToDec() > 127 ? (getType() == NORMAL ? up(138,10) :
                up(228,8)) : PLSToDec() <= 127 ? up(12*S,6*S) : -1;
        return mod == 0;
    }
    private boolean is16PSK5F() {
        int mod = atE9.is() ? -1 : PLSToDec() > 127 ? (getType() == NORMAL ? up(148,8) :
                up(246,4)) : PLSToDec() <= 127 ? up(18*S,6*S) : -1;
        return mod == 0;
    }
    private boolean is32APSK5F() {
        int mod = atE9.is() ? -1 : PLSToDec() > 127 ? (getType() == NORMAL ? up(156,8) :
                up(250,4)) : PLSToDec() <= 127 ? up(24*S,5*S) : -1;
        return mod == 0;
    }
    private int e8(boolean isQPSK, int spreadCode) {
        return spreadCode == 0 && isQPSK ? 5 : spreadCode == 1 && isQPSK ? 2 : 1;
    }
    private int mediumSz(boolean isQPSK) {
        return 90*(isQPSK && this.spread == 5 ? 960 : isQPSK && this.spread == 2 ? 384 : -1);
    }
    private int shortSz(boolean isQPSK, boolean isPSK, boolean is16PSK, boolean is32PSK) {
        return 90*(isQPSK && this.spread == 5 ? 480 : isQPSK && this.spread == 2 ? 192
                : isQPSK && this.spread == 1 ? 90 : this.spread == 1 && isPSK ? 60
                : is16PSK && this.spread == 1 ? 45 : is32PSK && this.spread == 1 ? 36 : -1);
    }
    private int normalSz(boolean isQPSK, boolean isPSK, boolean is16PSK, boolean is32PSK) {
        return 4 * shortSz(isQPSK, isPSK, is16PSK, is32PSK);//TODO: 64, 128, 256
    }
    public B(U8 pls, SFH sfh, SFFI eFormat, S2xSOF sf) {
        if (!accept(pls, eFormat.getType()))  // 12 or 17a,17b
            _isS2 =  eFormat.getType()==5 ? !atE9.is() : eFormat.getType()==4
                    ? !atE6.is() : _isS2;
        int typeX = getType();
        switch (eFormat.getType()) {
            case 0:
                typeX = typeX & (NORMAL | SHORT); // sosf+sffi
                this.size = typeX == NORMAL ? 30780 : 14976;
                this.spread = 1;
                typeX = sf == null ? typeX : typeX | PILOT; // sf pilots, PL pilots is not possible
                break;
            case 1:
                typeX = sf == null ? NORMAL : NORMAL | PILOT;
                this.spread = 30; // sosf+sffi+plh
                this.size = 64800;
                break;
            case 2:
                typeX = PLSToDec() == 64 ? -1 : PLSToDec() <= 107 ? NORMAL
                        : PLSToDec() <= 110 ? MEDIUM : PLSToDec() <= 112 ? SHORT : -1;
                //TODO: define pls from E3
                this.spread = 6;
                this.size = typeX == NORMAL ? 64800 : typeX == MEDIUM ? 32400 : 16200;
                typeX = typeX | sfh.getSFPilot(); // no b7
                break;
            case 3:
                typeX = PLSToDec() >= 84 ? -1 : SHORT | PILOT; //modulated and SF, no b7
                //TODO: define pls from E4
                this.spread = 4;
                this.size = 16200;
                break;
            case 4:
                int pilot = sfh != null ? sfh.getSFPilot() : 0;//sofs+sffi+sfh+st
                int sizeCode = PLSToDec() <= 127 ? (PLSToDec() & 0x3) << 1 : this.size == 64800
                        ? NORMAL : this.size == 32400 ? MEDIUM : SHORT;
                // E6, E7, E8
                typeX = PLSToDec() == 65 || PLSToDec() == 73 ? -1 : PLSToDec() <= 127
                        ? sizeCode | pilot : PLSToDec() <= 131 ? -1
                        : PLSToDec() <= 248 && PLSToDec() % 2 == 1
                        ? -1 : PLSToDec() <= 248 && PLSToDec() % 2 == 0 ? sizeCode | pilot : -1;
                this.modcod = typeX == -1 ? 0 : PLSToDec() <= 63 ? this.modcod
                        : PLSToDec() <= 127 ? PLSToDec()  >> 1 : this.modcod;
                this.spread = e8(isQPSK(), (PLSToDec() & 0x2) >> 1);
                this.size = sizeCode == MEDIUM ? mediumSz(isQPSK())
                        : (sizeCode & NORMAL) == NORMAL ? normalSz(isQPSK(), is8PSK(),
		 is16PSK(), is32APSK())  : shortSz(isQPSK(), is8PSK(), is16PSK(), is32APSK());               
                break;
            case 5:
                int lastFramePilot = typeX %2 | (sfh != null ? sfh.getSFPilot() : 0);//sofs+sffi+sfh+st
                sizeCode = atE9.is() ? atE9.getType() : this.size == 64800
                        ? NORMAL : this.size == 32400 ? MEDIUM : SHORT;
                typeX =  sizeCode | lastFramePilot;
                this.modcod = atE9.is() ? atE9.getModCod() : this.modcod;
                this.spread = e8(isQPSK5F(), atE9.is() ? atE9.spreadCode() : (typeX & 0x2) >> 1);
                this.size = sf != null ? sf.getSFL() : sizeCode == MEDIUM ? mediumSz(isQPSK5F())
                        : (sizeCode & NORMAL) == NORMAL
                        ? normalSz(isQPSK5F(), is8PSK5F(), is16PSK5F(), is32APSK5F())
                        : shortSz(isQPSK5F(), is8PSK5F(), is16PSK5F(), is32APSK5F());
               break;
        }
        this.typeX = new U3(typeX);
        this.sfh = sfh != null ? sfh : this.sfh;
        this.sf = sf != null ? sf : this.sf;
        this.eFormat = eFormat;
    }
    public B(U8 pls) {
        accept(pls, eFormat.getType());
    }    
    public B(U5 modcod, U2 type) {
        accept(modcod);
        this.typeX = new U3(type.getType());
    }
    private int PLSToDec() { return s2xPls.toDec() ;    }
    @Override    public int getModCod() {        return modcod;    }
    @Override    public int getType() {        return typeX.getType();    }
 @Override public String toString() { return (isS2()?"A(":"B(") + Integer.toString(getModCod()) + ")";}
    @Override    protected boolean isS2() {        return _isS2;    }
    @Override    public boolean isSF() {        return eFormat.isSF();    }
    @Override    public int getPDistance() {        return sf.getPDistance();    }
    @Override    public int getPSize() {        return sf.getPSize();    }
    @Override    public int getSFL() {        return sf.getSFL();    }
    @Override    public int getSize() {        return size;    }
    @Override    public int getSpread() {        return spread;    }
    @Override    public boolean isSheduledBHSC() {  return isSF() && eFormat.getType() == 5;    }
    @Override    public boolean isTrackedPlh() { return isSF() && eFormat.getType() == 4;}
    @Override    public boolean isReserved() {        return typeX.isReserved();    }
    protected int getHPointer() {        return sfh !=null ? sfh.getHPointer() : -1;    }
    protected int getPli() {        return sfh !=null ? sfh.getPli() : -1;    }
    protected int getSFPilot() {        return  sfh !=null ? sfh.getSFPilot() : -1;  }
}
class C extends B {
    static String JSON = "{\"modem\":{\"MODCOD\":\"%d\",\"TYPE\":\"%d\"}}";
    static String JSONX = "{\"modem\":{\"MODCODX\":\"%d\",\"TYPE\":\"%d\"}}";
    static String JSONXE = "{\"modem\":{\"MODCODX\":\"%d\",\"TYPE\":\"%d\"," +
            "\"SPREAD\":\"%d\",\"SIZE\":\"%d\",\"PLI\":\"%d,\"SFL\":\"%d\",\"FMT\":\"%d\"}}";
    static String JSONE = "{\"modem\":{\"MODCOD\":\"%d\",\"TYPE\":\"%d\"," +
            "\"SPREAD\":\"%d\",\"SIZE\":\"%d\",\"PLI\":\"%d,\"SFL\":\"%d\",\"FMT\":\"%d\"}}";
    public C(U8 pls, SFH sfh, SFFI eFormat, S2xSOF sf) {        super(pls,sfh,eFormat,sf);    }
    @Override
    public String toString() {
        boolean isE = isSheduledBHSC() || isTrackedPlh();
     return String.format( isE && isS2() ? JSONE : isE ? JSONXE : !isS2() ? JSONX : JSON, getModCod()  , getType(), getSpread(), getSize(), getPli(), getSFL() , isTrackedPlh() 
	? 4 : isSheduledBHSC() ? 5 : 0);
    }
}
public class DvbS2 {
    public static void main(String[] args) {
        C b1 = new C(new U8(1<<2|0x1), new SFH(0, 2, 0), new SFFI(5), null),
         b2 = new C(new U8(28<<2|0x3), new SFH(0, 2, 1), new SFFI(5), new SOF(20)),
         b3 = new C(new U8(114), new SFH(0, 2, 0), new SFFI(5), null);
        B b4 = new B(new U8(196), new SFH(0, 2, 0), new SFFI(5), null);        C b11 = new C(new U8(174), new SFH(0, 2, 1), new SFFI(4), null),
         b12 = new C(new U8(28<<1|0x1), new SFH(0, 2, 0), new SFFI(4), null),
         b13 = new C(new U8(66), new SFH(0, 2, 1), new SFFI(4), null);
        B a = new B(new U5(27), new U2(3));
       List<? extends B> s2xObservable = Arrays.asList(b1,b2,b3,b4, a,b11,b12,b13); // covariant s2x
        List<? super B> s2xModelObserver = new ArrayList();//Does contravariance s2x enough?
        s2xObservable.forEach(t -> s2xModelObserver.add(t));// Yes: no runtime s2x error
        System.out.println(s2xModelObserver);
    }
}
