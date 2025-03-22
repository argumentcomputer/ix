#[macro_export]
macro_rules! func {
    (fn $name:ident($( $in:ident $(: [$in_size:expr])? ),*): [$size:expr] $aiur:tt) => {{
        $(let $in = $crate::var!($in $(, $in_size)?);)*
        $crate::aiur::frontend::expr::FunctionE {
            name: stringify!($name),
            invertible: false,
            partial: false,
            input_params: [$($crate::var!($in $(, $in_size)?)),*].into(),
            output_size: $size,
            body: $crate::block_init!($aiur),
        }
    }};
    (partial fn $name:ident($( $in:ident $(: [$in_size:expr])? ),*): [$size:expr] $aiur:tt) => {{
        $(let $in = $crate::var!($in $(, $in_size)?);)*
        $crate::aiur::frontend::expr::FunctionE {
            name: stringify!($name),
            invertible: false,
            partial: true,
            input_params: [$($crate::var!($in $(, $in_size)?)),*].into(),
            output_size: $size,
            body: $crate::block_init!($aiur),
        }
    }};
    (invertible fn $name:ident($( $in:ident $(: [$in_size:expr])? ),*): [$size:expr] $aiur:tt) => {{
        $(let $in = $crate::var!($in $(, $in_size)?);)*
        $crate::aiur::frontend::expr::FunctionE {
            name: stringify!($name),
            invertible: true,
            partial: false,
            input_params: [$($crate::var!($in $(, $in_size)?)),*].into(),
            output_size: $size,
            body: $crate::block_init!($aiur),
        }
    }};
    (invertible partial fn $name:ident($( $in:ident $(: [$in_size:expr])? ),*): [$size:expr] $aiur:tt) => {{
        $(let $in = $crate::var!($in $(, $in_size)?);)*
        $crate::aiur::frontend::expr::FunctionE {
            name: stringify!($name),
            invertible: true,
            partial: true,
            input_params: [$($crate::var!($in $(, $in_size)?)),*].into(),
            output_size: $size,
            body: $crate::block_init!($aiur),
        }
    }};
}

#[macro_export]
macro_rules! var {
    ($variable:ident) => {{
        let name = $crate::aiur::frontend::expr::Ident::User(stringify!($variable));
        $crate::aiur::frontend::expr::Var { name, size: 8 }
    }};
    ($variable:ident, $size:expr) => {{
        let name = $crate::aiur::frontend::expr::Ident::User(stringify!($variable));
        $crate::aiur::frontend::expr::Var { name, size: $size }
    }};
}

#[macro_export]
macro_rules! block_init {
    ({ #[unconstrained] $($body:tt)+ }) => {{
        #[allow(unused_mut)]
        let mut ops = vec![];
        $crate::block!({ $($body)+ }, ops)
    }};
    ({ $($body:tt)+ }) => {{
        #[allow(unused_mut)]
        let mut ops = vec![];
        $crate::block!({ $($body)+ }, ops)
    }}
}

#[macro_export]
macro_rules! block {
    // Operations
    ({ let $tgt:ident = $a:literal; $($tail:tt)+ }, $ops:expr) => {{
        $ops.push($crate::aiur::frontend::expr::OpE::Prim($crate::var!($tgt), $a));
        let $tgt = $crate::var!($tgt);
        $crate::block!({ $($tail)* }, $ops)
    }};
    ({ let $tgt:ident = add($a:ident, $b:ident); $($tail:tt)+ }, $ops:expr) => {{
        let tgt_size = $a.size;
        $ops.push($crate::aiur::frontend::expr::OpE::Add($crate::var!($tgt, tgt_size), $a, $b));
        let $tgt = $crate::var!($tgt, tgt_size);
        $crate::block!({ $($tail)* }, $ops)
    }};
    ({ let $tgt:ident = sub($a:ident, $b:ident); $($tail:tt)+ }, $ops:expr) => {{
        let tgt_size = $a.size;
        $ops.push($crate::aiur::frontend::expr::OpE::Sub($crate::var!($tgt, tgt_size), $a, $b));
        let $tgt = $crate::var!($tgt, tgt_size);
        $crate::block!({ $($tail)* }, $ops)
    }};
    ({ let $tgt:ident = mul($a:ident, $b:ident); $($tail:tt)+ }, $ops:expr) => {{
        let tgt_size = $a.size;
        $ops.push($crate::aiur::frontend::expr::OpE::Mul($crate::var!($tgt, tgt_size), $a, $b));
        let $tgt = $crate::var!($tgt, tgt_size);
        $crate::block!({ $($tail)* }, $ops)
    }};
    ({ let $tgt:ident = store($($arg:ident),*); $($tail:tt)+ }, $ops:expr) => {{
        let inp = [$($arg),*].into();
        $ops.push($crate::aiur::frontend::expr::OpE::Store($crate::var!($tgt), inp));
        let $tgt = $crate::var!($tgt);
        $crate::block!({ $($tail)* }, $ops)
    }};
    ({ let $tgt:ident $(: [$size:expr])? = load($arg:ident); $($tail:tt)+ }, $ops:expr) => {{
        let out = [$crate::var!($tgt $(, $size)?)].into();
        $ops.push($crate::aiur::frontend::expr::OpE::Load(out, $arg));
        let $tgt = $crate::var!($tgt $(, $size)?);
        $crate::block!({ $($tail)* }, $ops)
    }};
    ({ let ($($tgt:ident $(: [$size:expr])?),*) = load($arg:ident); $($tail:tt)+ }, $ops:expr) => {{
        let out = [$($crate::var!($tgt $(, $size)?)),*].into();
        $ops.push($crate::aiur::frontend::expr::OpE::Load(out, $arg));
        $(let $tgt = $crate::var!($tgt $(, $size)?);)*
        $crate::block!({ $($tail)* }, $ops)
    }};
    ({ let ($($tgt:ident $(: [$size:expr])?),*) = call($name:ident, $($arg:ident),*); $($tail:tt)+ }, $ops:expr) => {{
        let func = stringify!($name);
        let out = [$($crate::var!($tgt $(, $size)?)),*].into();
        let inp = [$($arg),*].into();
        $ops.push($crate::aiur::frontend::expr::OpE::Call(out, func, inp));
        $(let $tgt = $crate::var!($tgt $(, $size)?);)*
        $crate::block!({ $($tail)* }, $ops)
    }};
    ({ let $tgt:ident $(: [$size:expr])? = call($name:ident, $($arg:ident),*); $($tail:tt)+ }, $ops:expr) => {{
        let func = stringify!($name);
        let out = [$crate::var!($tgt $(, $size)?)].into();
        let inp = [$($arg),*].into();
        $ops.push($crate::aiur::frontend::expr::OpE::Call(out, func, inp));
        let $tgt = $crate::var!($tgt $(, $size)?);
        $crate::block!({ $($tail)* }, $ops)
    }};
    ({ let ($($tgt:ident $(: [$size:expr])?),*) = extern_call($name:ident, $($arg:ident),*); $($tail:tt)+ }, $ops:expr) => {{
        let func = stringify!($name);
        let out = [$($crate::var!($tgt $(, $size)?)),*].into();
        let inp = [$($arg),*].into();
        $ops.push($crate::aiur::frontend::expr::OpE::ExternCall(out, func, inp));
        $(let $tgt = $crate::var!($tgt $(, $size)?);)*
        $crate::block!({ $($tail)* }, $ops)
    }};
    // Control statements
    ({ return ($($src:ident),*) }, $ops:expr) => {{
        let ops = $ops.into();
        let ctrl = $crate::aiur::frontend::expr::CtrlE::Return([$($src),*].into());
        $crate::aiur::frontend::expr::BlockE { ops, ctrl }
    }};
    ({ return $src:ident }, $ops:expr) => {{
        let ops = $ops.into();
        let ctrl = $crate::aiur::frontend::expr::CtrlE::Return([$src].into());
        $crate::aiur::frontend::expr::BlockE { ops, ctrl }
    }};
    ({ if $x:ident { $($true_block:tt)+ } $($false_block:tt)+ }, $ops:expr) => {{
        let ops = $ops.into();
        let true_block = Box::new($crate::block_init!({ $($true_block)+ }));
        let false_block = Box::new($crate::block_init!({ $($false_block)+ }));
        let ctrl = $crate::aiur::frontend::expr::CtrlE::If($x, true_block, false_block);
        $crate::aiur::frontend::expr::BlockE { ops, ctrl }
    }};
    ({ if !$x:ident { $($true_block:tt)+ } $($false_block:tt)+ }, $ops:expr) => {{
        let ops = $ops.into();
        let true_block = Box::new($crate::block_init!({ $($true_block)+ }));
        let false_block = Box::new($crate::block_init!({ $($false_block)+ }));
        let ctrl = $crate::aiur::frontend::expr::CtrlE::If($x, false_block, true_block);
        $crate::aiur::frontend::expr::BlockE { ops, ctrl }
    }};
}

#[macro_export]
macro_rules! constrained {
    ({ #[unconstrained] $($body:tt)+ }) => {
        $crate::aiur::frontend::expr::CaseType::Unconstrained
    };
    ({ $($body:tt)+ }) => {
        $crate::aiur::frontend::expr::CaseType::Constrained
    };
}
