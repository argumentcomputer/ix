import Aiur.Modules.Frontend

/-! Joint-window G1 multi-scalar multiplication. Scalar limbs are canonical
below Fr. Four-bit recurrences have bounded digits and fixed zero endpoints,
so each 80-bit limb is interpreted as an integer without Fr wraparound.
Point tables and every group operation are computed by ordinary Aiur code. -/
namespace MultiStark.Source

def kzgMsm : Aiur.Modules.Program Nat := aiur⟦
module KzgMsm {
  type Point = BN254G1::Point;
  type Table = Lists::List<Point>;
  type Prepared = Lists::List<(Table, [Field;4])>;
  type Terms = Lists::List<(Table, Field)>;

  fn table_rows(point: Point, value: Point, count: Field) -> Table {
    match count {
      1 => &(Lists::Node::Cons(value,&(Lists::Node::Nil))),
      _ => &(Lists::Node::Cons(value,table_rows(point,BN254G1::add(value,point),count-1))),
    }
  }

  fn table(point: Point) -> Table { table_rows(point,BN254G1::INFINITY,16) }

  fn prepare(terms: Lists::List<(Point,Field)>) -> Prepared {
    match *terms {
      Lists::Node::Nil => &(Lists::Node::Nil),
      Lists::Node::Cons((point,scalar),rest) =>
        &(Lists::Node::Cons((table(point),BN254G1::scalar_limbs(scalar)),prepare(rest))),
    }
  }

  fn limb(terms: Prepared, index: Field) -> Terms {
    match *terms {
      Lists::Node::Nil => &(Lists::Node::Nil),
      Lists::Node::Cons((points,limbs),rest) => {
        let value = match index {0=>limbs[0],1=>limbs[1],2=>limbs[2],3=>limbs[3]};
        &(Lists::Node::Cons((points,value),limb(rest,index)))
      },
    }
  }

  fn split(terms: Terms) -> (Terms,Lists::List<Point>) {
    match *terms {
      Lists::Node::Nil => (&(Lists::Node::Nil),&(Lists::Node::Nil)),
      Lists::Node::Cons((points,value),rest) => {
        let (quotient,digit) = hint::<(Field,Field)>("kzg.msm.window4",value);
        BN254Fq::byte(digit); BN254Fq::byte(16*digit);
        assert_eq!(16*quotient+digit,value,"KZG MSM window recurrence");
        let (next,selected) = split(rest);
        let next = &(Lists::Node::Cons((points,quotient),next));
        match digit {
          0 => (next,selected),
          _ => (next,&(Lists::Node::Cons(Lists::lookup(points,digit),selected))),
        }
      },
    }
  }

  fn finish(terms: Terms) -> () {
    match *terms {
      Lists::Node::Nil => (),
      Lists::Node::Cons((_points,value),rest) => {
        assert_eq!(value,0,"KZG MSM window endpoint"); finish(rest)
      },
    }
  }

  fn add_points(points: Lists::List<Point>, accumulator: Point) -> Point {
    match *points {
      Lists::Node::Nil => accumulator,
      Lists::Node::Cons(point,rest) => add_points(rest,BN254G1::add(accumulator,point)),
    }
  }

  fn windows(terms: Terms, count: Field, accumulator: Point) -> Point {
    match count {
      0 => {finish(terms); accumulator},
      _ => {
        let (next,selected) = split(terms);
        let accumulator = windows(next,count-1,accumulator);
        let accumulator = BN254G1::double(BN254G1::double(BN254G1::double(BN254G1::double(accumulator))));
        add_points(selected,accumulator)
      },
    }
  }

  fn msm(terms: Lists::List<(Point,Field)>) -> Point {
    let prepared = prepare(terms);
    let a = windows(limb(prepared,3),4,BN254G1::INFINITY);
    let b = windows(limb(prepared,2),20,a);
    let c = windows(limb(prepared,1),20,b);
    windows(limb(prepared,0),20,c)
  }
}
⟧

end MultiStark.Source
