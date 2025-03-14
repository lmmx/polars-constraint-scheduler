import polars as pl
import pytest
from polars_scheduler import SchedulerPlugin


@pytest.mark.failing(reason="Schedules both at 7am")
@pytest.mark.parametrize(
    "frequency, expected_height",
    [
        ("1x daily", 1),
        ("2x daily", 2),
        ("3x daily", 3),
        ("9x daily", 9),
        ("10x daily", 10),
        ("100x daily", 100),
    ],
)
def test_daily_frequency(frequency, expected_height):
    """Test '_x daily' frequency."""
    df = pl.DataFrame(
        {
            "Event": ["pill"],
            "Category": ["medication"],
            "Unit": ["pill"],
            "Amount": [None],
            "Divisor": [None],
            "Frequency": [frequency],
            "Constraints": [[]],
            "Windows": [[]],
            "Note": [None],
        }
    )

    scheduler = SchedulerPlugin(df)
    result = scheduler.schedule()
    assert result.height == expected_height
