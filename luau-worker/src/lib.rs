use futures_util::StreamExt;
use base64::prelude::*;
use luau_lifter::decompile_bytecode;
use serde::{Deserialize, Serialize};
use worker::*;

// Security: Consider moving to environment variable or KV storage
const AUTH_SECRET: &str = "ymjKH2O3BbO3bDSsKmpo3ek3vHxIWYLQfj0";

// Configuration constants
const MAX_BYTECODE_SIZE: usize = 10 * 1024 * 1024; // 10MB limit
const WEBSOCKET_VERSION: u8 = 1;
const HTTP_VERSION: u8 = 203;

#[derive(Deserialize)]
struct DecompileMessage {
    id: String,
    encoded_bytecode: String,
}

#[derive(Serialize)]
struct DecompileResponse {
    id: String,
    decompilation: String,
}

#[derive(Serialize)]
struct ErrorResponse {
    error: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    details: Option<String>,
}

impl ErrorResponse {
    fn new(error: impl Into<String>) -> Self {
        Self {
            error: error.into(),
            details: None,
        }
    }

    fn with_details(error: impl Into<String>, details: impl Into<String>) -> Self {
        Self {
            error: error.into(),
            details: Some(details.into()),
        }
    }

    fn to_json(&self) -> String {
        serde_json::to_string(self).unwrap_or_else(|_| r#"{"error":"serialization failed"}"#.to_string())
    }
}

/// Validates the authorization header against the configured secret
fn validate_authorization(headers: &Headers) -> Result<()> {
    let auth_header = headers
        .get("Authorization")?
        .ok_or_else(|| Error::RustError("Authorization header is required".to_string()))?;

    if auth_header != AUTH_SECRET {
        return Err(Error::RustError("Invalid authorization token".to_string()));
    }

    Ok(())
}

/// Decodes and validates base64-encoded bytecode
fn decode_bytecode(encoded: &str) -> Result<Vec<u8>> {
    let bytecode = BASE64_STANDARD
        .decode(encoded)
        .map_err(|e| Error::RustError(format!("Invalid base64 encoding: {}", e)))?;

    if bytecode.is_empty() {
        return Err(Error::RustError("Bytecode cannot be empty".to_string()));
    }

    if bytecode.len() > MAX_BYTECODE_SIZE {
        return Err(Error::RustError(format!(
            "Bytecode too large (max {} bytes)",
            MAX_BYTECODE_SIZE
        )));
    }

    Ok(bytecode)
}

/// Handles WebSocket decompilation requests
async fn handle_websocket(req: Request) -> Result<Response> {
    validate_authorization(&req.headers())?;

    let pair = WebSocketPair::new()?;
    let server = pair.server;
    server.accept()?;

    wasm_bindgen_futures::spawn_local(async move {
        if let Err(e) = handle_websocket_events(server).await {
            console_error!("WebSocket error: {:?}", e);
        }
    });

    Response::from_websocket(pair.client)
}

/// Processes WebSocket events and decompilation messages
async fn handle_websocket_events(server: WebSocket) -> Result<()> {
    let mut event_stream = server.events()?;

    while let Some(event) = event_stream.next().await {
        match event {
            Ok(WebsocketEvent::Message(msg)) => {
                if let Err(e) = process_websocket_message(&server, msg).await {
                    console_error!("Message processing error: {:?}", e);
                    let error_response = ErrorResponse::new(format!("{:?}", e));
                    let _ = server.send_with_str(&error_response.to_json());
                }
            }
            Ok(WebsocketEvent::Close(_)) => {
                console_log!("WebSocket closed");
                break;
            }
            Err(e) => {
                console_error!("WebSocket event error: {:?}", e);
                break;
            }
        }
    }

    Ok(())
}

/// Processes a single WebSocket message
async fn process_websocket_message(server: &WebSocket, msg: WebsocketIncomingMessage) -> Result<()> {
    let decompile_msg = msg
        .json::<DecompileMessage>()
        .map_err(|e| Error::RustError(format!("Invalid message format: {}", e)))?;

    let bytecode = decode_bytecode(&decompile_msg.encoded_bytecode)?;
    
    let decompilation = std::panic::catch_unwind(|| {
        decompile_bytecode(&bytecode, WEBSOCKET_VERSION)
    })
    .unwrap_or_else(|_| "Decompilation failed: internal error".to_string());

    let response = DecompileResponse {
        id: decompile_msg.id,
        decompilation,
    };

    let response_json = serde_json::to_string(&response)
        .map_err(|e| Error::RustError(format!("Failed to serialize response: {}", e)))?;

    server.send_with_str(&response_json)?;

    Ok(())
}

/// Handles HTTP POST decompilation requests
async fn handle_http_decompile(mut req: Request) -> Result<Response> {
    validate_authorization(&req.headers())?;

    let encoded_bytecode = req.bytes().await?;

    // Convert bytes to string for base64 decoding
    let encoded_str = std::str::from_utf8(&encoded_bytecode)
        .map_err(|e| Error::RustError(format!("Invalid UTF-8 in request body: {}", e)))?;

    let bytecode = decode_bytecode(encoded_str)?;

    // Catch panics during decompilation
    let decompilation = std::panic::catch_unwind(|| {
        decompile_bytecode(&bytecode, HTTP_VERSION)
    })
    .unwrap_or_else(|_| {
        console_error!("Decompilation panicked");
        "Decompilation failed: internal error".to_string()
    });

    Response::ok(decompilation)
}

/// Health check endpoint
async fn handle_health_check(_req: Request) -> Result<Response> {
    Response::ok("OK")
}

/// Returns a proper JSON error response
fn json_error(message: impl Into<String>, status: u16) -> Result<Response> {
    let error = ErrorResponse::new(message);
    Response::error(error.to_json(), status)
}

#[event(fetch, respond_with_errors)]
pub async fn main(req: Request, env: Env, _ctx: worker::Context) -> Result<Response> {
    // Set panic hook once for better error messages
    console_error_panic_hook::set_once();

    let router = Router::new();
    
    router
        .get_async("/health", handle_health_check)
        .get_async("/decompile_ws", |req, _ctx| async move {
            handle_websocket(req).await.or_else(|e| {
                console_error!("WebSocket handler error: {:?}", e);
                json_error(format!("WebSocket error: {:?}", e), 500)
            })
        })
        .post_async("/decompile", |req, _ctx| async move {
            handle_http_decompile(req).await.or_else(|e| {
                console_error!("HTTP decompile error: {:?}", e);
                
                // Determine appropriate status code
                let status = if e.to_string().contains("Authorization") {
                    403
                } else if e.to_string().contains("Invalid") || e.to_string().contains("empty") {
                    400
                } else {
                    500
                };
                
                json_error(format!("{:?}", e), status)
            })
        })
        .run(req, env)
        .await
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_decode_bytecode_empty() {
        let result = decode_bytecode("");
        assert!(result.is_err());
    }

    #[test]
    fn test_decode_bytecode_invalid_base64() {
        let result = decode_bytecode("not-valid-base64!!!");
        assert!(result.is_err());
    }

    #[test]
    fn test_decode_bytecode_valid() {
        // "Hello" in base64
        let result = decode_bytecode("SGVsbG8=");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), b"Hello");
    }

    #[test]
    fn test_error_response_serialization() {
        let error = ErrorResponse::new("test error");
        let json = error.to_json();
        assert!(json.contains("test error"));
    }

    #[test]
    fn test_error_response_with_details() {
        let error = ErrorResponse::with_details("main error", "detailed info");
        let json = error.to_json();
        assert!(json.contains("main error"));
        assert!(json.contains("detailed info"));
    }
}
