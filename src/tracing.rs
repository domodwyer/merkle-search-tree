#[cfg(test)]
pub(crate) static LOGGING_INIT: std::sync::Once = std::sync::Once::new();

/// Emit a debug event if the "tracing" feature is enabled.
macro_rules! debug {
    (
		$($t:tt)+
	) => {
		#[cfg(any(test, feature = "tracing"))]
        ::tracing::debug!($($t)+);
    };
}

/// Emit a trace event if the "tracing" feature is enabled.
macro_rules! trace {
    (
		$($t:tt)+
	) => {
		#[cfg(any(test, feature = "tracing"))]
        ::tracing::trace!($($t)+);
    };
}

/// Enable event logging for tests.
#[cfg(test)]
macro_rules! enable_logging {
    () => {{
        crate::tracing::LOGGING_INIT.call_once(|| {
            let subscriber = ::tracing_subscriber::FmtSubscriber::builder()
                .with_env_filter("trace")
                .with_test_writer()
                .pretty()
                .finish();

            ::tracing::subscriber::set_global_default(subscriber)
                .expect("failed to enable test logging");
        });
    }};
}
