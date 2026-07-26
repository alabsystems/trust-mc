<!-- dscan:allow(volatile_numbers) -->
# Benchmarks

Docker-based evaluation harness templates for reproducible benchmarks.

## Usage

```bash
# Copy templates to set up benchmarking
cp -r templates/* .

# Run evaluation
./run_eval.sh --suite default

# Or use Docker
docker compose up --build
```

## Files

- `templates/` - Copy these files to start
  - `Dockerfile` - Container definition
  - `docker-compose.yaml` - Compose configuration
  - `run_eval.sh` - Evaluation runner script

## Documentation

See `benchmarking.md` at the repository root for full documentation.
